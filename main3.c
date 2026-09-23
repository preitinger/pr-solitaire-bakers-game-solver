#define _GNU_SOURCE
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdarg.h>
#include <sys/stat.h>
#include <inttypes.h>

#define ARENA_SIZE (256ULL * 1024 * 1024 << 2) // 1024 MB of main memory for states
// ~67 million buckets (needs only about 268 MB of RAM for hash_buckets)
#define HASH_TABLE_SIZE 67108859 // prime number
// #define HASH_TABLE_SIZE 8388607             // prime number for open addressing
#define MAX_DEPTH 2000000
#define NUM_COLUMNS 8
#define NUM_FREECELLS 4
#define COLORED
#ifdef COLORED
#define ANSI_ROT "\x1b[31m"
#define ANSI_RESET "\x1b[0m"
#else
#define ANSI_ROT ""   //"\x1b[31m"
#define ANSI_RESET "" // "\x1b[0m"
#endif

static inline int min(int a, int b)
{
    if (a < b)
        return a;
    return b;
}

// --- TYPES & STRUCTURES ---

// Suits: 0 = spades, 1 = hearts, 2 = diamonds, 3 = clubs
// Rank:  0 (ace) through 12 (king)
// Formula: card = (rank * 4) + suit (0..51, 255 = empty)

typedef struct
{
    uint8_t columns[NUM_COLUMNS][19];
    uint8_t col_lens[NUM_COLUMNS];
    uint8_t freecells[NUM_FREECELLS]; // 255 = empty
    uint8_t foundations[4];           // Highest solved rank (0 = none, 1 = ace, ..., 13 = king)
} GameState;

typedef enum
{
    MOVE_TABLEAU_TO_FOUNDATION,
    MOVE_FREECELL_TO_FOUNDATION,
    MOVE_TABLEAU_TO_TABLEAU,
    MOVE_TABLEAU_TO_FREECELL,
    MOVE_FREECELL_TO_TABLEAU
} MoveType;

typedef struct
{
    MoveType type;
    uint8_t src;
    uint8_t dst;
    uint8_t card;
    uint8_t count; // NEW: number of cards moved (for meta-moves)
    GameState gameState;
} Move;

// --- GLOBAL MEMORY SYSTEMS ---

static uint8_t *arena_buffer = NULL;
static size_t arena_offset = 0;
static uint32_t *hash_buckets = NULL;

static Move move_history[MAX_DEPTH];
static int total_solution_moves = 0;
static uint64_t steps = 0;

const char *suits[] = {"♠", "♥", "♦", "♣"};
const char *ranks[] = {" A", " 2", " 3", " 4", " 5", " 6", " 7", " 8", " 9", "10", " J", " Q", " K"};

// --- ARITHMETIC & HELPERS ---

uint8_t make_card(uint8_t rank_1_to_13, uint8_t suit_0_to_3)
{
    return ((rank_1_to_13 - 1) << 2) | (suit_0_to_3 & 3);
}

// --- CANONICAL PACKING & HASH SET ---

int compColumn(const void *a1, const void *b1, void *s1)
{
    const int *a = (const int *)a1;
    const int *b = (const int *)b1;
    const GameState *s = (const GameState *)s1;
    // 1. Empty columns first
    // 2. Then compare the first card

    bool emptyA = s->col_lens[*a] == 0;
    bool emptyB = s->col_lens[*b] == 0;

    if (emptyA)
    {
        if (emptyB)
        {
            return 0;
        }
        else
        {
            return -1;
        }
    }
    else
    {
        if (emptyB)
        {
            return 1;
        }
        else
        {
            return (int)s->columns[*a][0] - (int)s->columns[*b][0];
        }
    }
}

int pack_state(const GameState *s, uint8_t *buf)
{
    int idx = 0;

    // 1. Foundations (4 Bytes)
    for (int i = 0; i < 4; i++)
        buf[idx++] = s->foundations[i];

    // 2. Sort FreeCells (symmetry breaking) and pack them (NUM_FREECELLS bytes)
    uint8_t fc[NUM_FREECELLS];
    memcpy(fc, s->freecells, NUM_FREECELLS);
    for (int i = 0; i < 3; i++)
    {
        for (int j = i + 1; j < NUM_FREECELLS; j++)
        {
            if (fc[i] > fc[j])
            {
                uint8_t tmp = fc[i];
                fc[i] = fc[j];
                fc[j] = tmp;
            }
        }
    }
    for (int i = 0; i < NUM_FREECELLS; i++)
        buf[idx++] = fc[i];

    // 3. Sort tableau columns
    int sorted[NUM_COLUMNS];
    for (int i = 0; i < NUM_COLUMNS; ++i)
    {
        sorted[i] = i;
    }
    qsort_r(sorted, NUM_COLUMNS, sizeof(int), &compColumn, (void *)s);

    // TODO permutate sorted so that columns are sorted

    // 3. Tableau columns
    for (int colI = 0; colI < NUM_COLUMNS; colI++)
    {
        int col = sorted[colI];
        buf[idx++] = s->col_lens[col];
        for (int i = 0; i < s->col_lens[col]; i++)
        {
            buf[idx++] = s->columns[col][i];
        }
    }

    return idx; // Exact total length
}

uint32_t hash_bytes(const uint8_t *data, size_t len)
{
    uint32_t hash = 2166136261u;
    for (size_t i = 0; i < len; i++)
    {
        hash ^= data[i];
        hash *= 16777619u;
    }
    return hash;
}

void print_game_state(const GameState *s);

bool is_visited_or_add(const GameState *state, uint32_t *arenaIndex)
{
    static uint32_t maxProbes = 0;
    ++steps;

    if (steps % 2000000 == 0)
    // if (steps > 12000)
    // if (true)
    {
        printf("\n>>> SNAPSHOT after %" PRIu64 " states (arena: %.2f MB) <<<\n",
               steps,
               (double)arena_offset / (1024.0 * 1024.0));
        print_game_state(state);
    }

    uint8_t tmp_buf[64];
    int len = pack_state(state, tmp_buf);

    uint32_t hash = hash_bytes(tmp_buf, len);
    uint32_t index = hash % HASH_TABLE_SIZE;
    uint32_t probes = 0;

    // Search for a free slot OR the chosen state
    while (hash_buckets[index] != 0)
    {
        uint32_t existing_offset = hash_buckets[index] - 1;
        uint8_t *existing_data = &arena_buffer[existing_offset];

        if (memcmp(existing_data, tmp_buf, len) == 0)
        {
            return true; // Already visited!
        }

        index = (index + 1) % HASH_TABLE_SIZE;
        probes++;

        // THE PROBES GUARD (prevents getting stuck!):
        if (probes >= HASH_TABLE_SIZE)
        {
            fprintf(stderr, "\n[ERROR] Hash table is full (%d buckets)! Please increase HASH_TABLE_SIZE.\n", HASH_TABLE_SIZE);
            exit(1);
        }
    }

    if (probes > maxProbes)
    {
        maxProbes = probes;
        printf("maxProbes: %d - steps: %" PRIu64 "\n", maxProbes, steps);
    }

    // New -> write into the arena
    if (arena_offset + len > ARENA_SIZE)
    {
        fprintf(stderr, "\n[ERROR] Arena memory is full!\n");
        exit(1);
    }

    uint32_t new_offset = (uint32_t)arena_offset;
    *arenaIndex = new_offset;
    memcpy(&arena_buffer[new_offset], tmp_buf, len);
    hash_buckets[index] = new_offset + 1; // 1-based offset
    arena_offset += len;

    return false; // State was new
}
// --- CORE RECURSION & LOGIC ---

bool is_solved(const GameState *state)
{
    return state->foundations[0] == 13 && state->foundations[1] == 13 &&
           state->foundations[2] == 13 && state->foundations[3] == 13;
}

// Calculates how many cards may be moved at once
int max_movable_cards(int free_cells, int empty_cols, bool dst_is_empty)
{
    if (dst_is_empty)
    {
        // If the destination is empty, that column is not available as temporary storage
        if (empty_cols == 0)
            return free_cells + 1;
        return (free_cells + 1) * (1 << (empty_cols - 1));
    }
    else
    {
        return (free_cells + 1) * (1 << empty_cols);
    }
}

// Returns the length of the valid sequence at the end of col (at least 1)
int get_sequence_length(const GameState *s, int col)
{
    int len = s->col_lens[col];
    if (len <= 1)
        return len;

    int seq_len = 1;
    for (int i = len - 1; i > 0; i--)
    {
        uint8_t card_below = s->columns[col][i];
        uint8_t card_above = s->columns[col][i - 1];

        uint8_t suit_below = card_below & 3;
        uint8_t rank_below = card_below >> 2;

        uint8_t suit_above = card_above & 3;
        uint8_t rank_above = card_above >> 2;

        // Baker's Game: same suit and rank exactly one lower
        if (suit_below == suit_above && rank_below + 1 == rank_above)
        {
            seq_len++;
        }
        else
        {
            break; // Sequence broken
        }
    }
    return seq_len;
}

bool seqInFreecells(GameState *state, int freecell)
{
    // Is the next-higher card of the same suit as the card in `freecell` in another FreeCell or the top reachable card of a column?
    // If so, the higher card should be played instead, and this one must not be played.
    int card = state->freecells[freecell];
    if (card < 52)
    {
        int nextCard = card + 4;
        if (nextCard < 52)
        {
            for (int f = 0; f < NUM_FREECELLS; ++f)
            {
                if (state->freecells[f] == nextCard)
                {
                    return true;
                }
            }
        }
    }

    return false;
}

// Does not check, if there are enough free cells and/or columns available.
int fittingColumnDst(GameState *state, uint8_t card)
{
    // First, search non-empty column onto which card can be laid.
    // Remember the last visited empty column.
    int empty = -1;
    for (int c = NUM_COLUMNS - 1; c >= 0; --c)
    {
        if (state->col_lens[c] == 0)
        {
            empty = c;
        }
        else
        {
            if (card + 4 == state->columns[c][state->col_lens[c] - 1])
                return c;
        }
    }

    // Now, if an empty column exists, the lowest one of them is set in empty. Otherwise, empty == -1 which means no column does fit.
    // So return empty here.
    return empty;
}

bool solve(GameState *state, int depth);

bool tryOntoEmptyColumn(GameState *state, int src, int dst, int seq_len,
                        int max_cards, int depth, uint8_t top_card_of_group)
{
    // DESTINATION COLUMN IS EMPTY:
    // Move only if:
    // 1. The sequence is not already the ENTIRE column (pointless isomorphism move).
    // 2. The sequence is within the max-movable limit.
    // NEW
    // 3. The next-higher card above the highest card of the moved sequence is not also reachable.
    if (seq_len < state->col_lens[src] && seq_len <= max_cards)
    {
        int sl = seq_len;

        // --- MAKE THE MOVE ---
        int src_start = state->col_lens[src] - sl;
        for (int i = 0; i < sl; i++)
        {
            state->columns[dst][i] = state->columns[src][src_start + i];
            state->columns[src][src_start + i] = 255;
        }
        state->col_lens[src] -= sl;
        state->col_lens[dst] = sl;

        move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)sl, *state};

        if (solve(state, depth + 1))
            return true;

        // --- BACKTRACK ---
        state->col_lens[src] += sl;
        state->col_lens[dst] = 0;
        for (int i = 0; i < sl; i++)
        {
            state->columns[src][src_start + i] = state->columns[dst][i];
            state->columns[dst][i] = 255;
        }
    }

    return false;
}

int findFreeCol(GameState *state)
{
    for (int c = 0; c < NUM_COLUMNS; ++c)
    {
        if (state->col_lens[c] == 0)
            return c;
    }
    return -1;
}

bool solve(GameState *state, int depth)
{
    // print_game_state(state);
    if (is_solved(state))
    {
        total_solution_moves = depth;
        return true;
    }
    if (depth >= MAX_DEPTH)
    {
        printf("\n\nMAX DEPTH - aborting!\n\n");
        return false;
    }

    // Check whether this state is already in the arena/hash table
    uint32_t arenaIndex = -1;
    if (is_visited_or_add(state, &arenaIndex))
        return false;

    // =========================================================================
    // 1. AUTO-MOVES (DOMINANCE RULE FOR BAKER'S GAME)
    // =========================================================================

    // Auto-Move: Tableau -> Foundation
    for (int col = 0; col < NUM_COLUMNS; col++)
    {
        if (state->col_lens[col] > 0)
        {
            uint8_t card = state->columns[col][state->col_lens[col] - 1];
            uint8_t suit = card & 3;
            uint8_t rank = (card >> 2) + 1;

            if (rank == state->foundations[suit] + 1)
            {
                // Make the move and clear the slot
                state->foundations[suit]++;
                state->col_lens[col]--;
                state->columns[col][state->col_lens[col]] = 255; // CLEAR!

                move_history[depth] = (Move){MOVE_TABLEAU_TO_FOUNDATION, col, suit, card, 0, *state};

                bool res = solve(state, depth + 1);

                // Backtrack
                state->columns[col][state->col_lens[col]] = card; // RESTORE
                state->col_lens[col]++;
                state->foundations[suit]--;

                return res; // HARD CUTOFF!
            }
        }
    }

    // Auto-Move: FreeCell -> Foundation
    for (int f = 0; f < NUM_FREECELLS; f++)
    {
        if (state->freecells[f] != 255)
        {
            uint8_t card = state->freecells[f];
            uint8_t suit = card & 3;
            uint8_t rank = (card >> 2) + 1;

            if (rank == state->foundations[suit] + 1)
            {
                // Make the move
                state->foundations[suit]++;
                state->freecells[f] = 255; // CLEAR!

                move_history[depth] = (Move){MOVE_FREECELL_TO_FOUNDATION, f, suit, card, 0, *state};

                bool res = solve(state, depth + 1);

                // Backtrack
                state->freecells[f] = card; // RESTORE
                state->foundations[suit]--;

                return res; // HARD CUTOFF!
            }
        }
    }

    // =========================================================================
    // 2. NORMAL BACKTRACKING (TABLEAU AND FREECELLS)
    // =========================================================================

    // A) Tableau -> Tableau (INCLUDING META-MOVES / SUPERMOVES)
    // Rules:
    // - Not onto empty column if fits on other column.

    {
        int free_cells_count = 0;
        for (int f = 0; f < NUM_FREECELLS; f++)
        {
            if (state->freecells[f] == 255)
                free_cells_count++;
        }

        int empty_cols_count = 0;
        for (int c = 0; c < NUM_COLUMNS; c++)
        {
            if (state->col_lens[c] == 0)
                empty_cols_count++;
        }

        for (int src = 0; src < NUM_COLUMNS; src++)
        {
            if (state->col_lens[src] == 0)
                continue;

            // Length of the contiguous sequence at the end of src
            int seq_len = get_sequence_length(state, src);
            uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - seq_len];
            int dst = fittingColumnDst(state, top_card_of_group);

            // for (int dst = 0; dst < NUM_COLUMNS; dst++)
            if (dst != -1)
            {
                // if (src == dst)
                // continue;

                bool dst_is_empty = (state->col_lens[dst] == 0);

                // Calculate maximum capacity
                int current_empty_cols = empty_cols_count - (dst_is_empty ? 1 : 0);
                int max_cards = max_movable_cards(free_cells_count, current_empty_cols, dst_is_empty);

                if (dst_is_empty)
                {
                    if (tryOntoEmptyColumn(state, src, dst, seq_len,
                                           max_cards, depth, top_card_of_group))
                        return true;
                }
                else
                {
                    // DESTINATION COLUMN IS NOT EMPTY:
                    uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];

                    if (seq_len <= max_cards) // Makes only sense, if can be moved completely.
                    {
                        int sl = seq_len;
                        uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - sl];

                        // Baker's Game rule: same suit (same symbol), rank exactly 1 lower.
                        // (top_card_of_group + 4) == dst_card
                        if ((top_card_of_group + 4) == dst_card)
                        {
                            // --- MAKE THE MOVE ---
                            int src_start = state->col_lens[src] - sl;
                            for (int i = 0; i < sl; i++)
                            {
                                state->columns[dst][state->col_lens[dst] + i] = state->columns[src][src_start + i];
                                state->columns[src][src_start + i] = 255;
                            }
                            state->col_lens[src] -= sl;
                            state->col_lens[dst] += sl;

                            move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)sl, *state};

                            if (solve(state, depth + 1))
                            {
                                return true;
                            }

                            // --- BACKTRACK ---
                            state->col_lens[dst] -= sl;
                            state->col_lens[src] += sl;
                            for (int i = 0; i < sl; i++)
                            {
                                state->columns[src][src_start + i] = state->columns[dst][state->col_lens[dst] + i];
                                state->columns[dst][state->col_lens[dst] + i] = 255;
                            }
                        }
                    }

                    // If the actions above were not successful, we have to check the move onto a free column, if there is any.
                    int dst = findFreeCol(state);

                    if (dst != -1)
                    {
                        if (tryOntoEmptyColumn(state, src, dst, seq_len,
                                               max_cards, depth, top_card_of_group))
                            return true;
                    }
                }
            }
        }
    }

    // B) Tableau -> FreeCells (ATOMIC META-MOVE & SINGLE MOVES)

    {
        // Count free FreeCells and collect their indexes
        int free_cells_count = 0;
        int free_indices[NUM_FREECELLS];
        for (int f = 0; f < NUM_FREECELLS; f++)
        {
            if (state->freecells[f] == 255)
            {
                free_indices[free_cells_count++] = f;
            }
        }

        if (free_cells_count > 0)
        {
            for (int src = 0; src < NUM_COLUMNS; src++)
            {
                int len = state->col_lens[src];
                if (len == 0)
                    continue;

                int seq_len = get_sequence_length(state, src);

                // CASE 1: Place a single card (seq_len == 1) into a FreeCell
                if (seq_len == 1)
                {
                    int f_slot = free_indices[0];
                    uint8_t card = state->columns[src][len - 1];
                    // war nur zum debuggen:
                    // const char *suit = suits[card & 3];
                    // const char *rank = ranks[card >> 2];

                    state->freecells[f_slot] = card;
                    state->columns[src][len - 1] = 255;
                    state->col_lens[src]--;

                    move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src, (uint8_t)f_slot, card, 1, *state};

                    if (solve(state, depth + 1))
                        return true;

                    // Backtrack
                    state->col_lens[src]++;
                    state->columns[src][len - 1] = card;
                    state->freecells[f_slot] = 255;
                }
                // CASE 2: Atomic meta-move - evacuate an ENTIRE sequence into FreeCells
                else if (seq_len > 1 && seq_len <= free_cells_count && len > seq_len)
                {
                    // Place ALL seq_len cards of the sequence into FreeCells at once
                    // in order to expose the non-sequence card UNDERNEATH.
                    uint8_t card;
                    // MAKE THE MOVE
                    for (int i = 0; i < seq_len; i++)
                    {
                        card = state->columns[src][len - 1 - i];
                        int f_slot = free_indices[i];
                        state->freecells[f_slot] = card;
                        state->columns[src][len - 1 - i] = 255;
                    }
                    state->col_lens[src] -= seq_len;

                    // Record it in the history (e.g. count = seq_len)
                    move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src, (uint8_t)free_indices[0],
                                                 card, (uint8_t)seq_len, *state};

                    if (solve(state, depth + 1))
                        return true;

                    // BACKTRACK
                    state->col_lens[src] += seq_len;
                    for (int i = seq_len - 1; i >= 0; i--)
                    {
                        int f_slot = free_indices[i];
                        uint8_t card = state->freecells[f_slot];
                        state->columns[src][len - 1 - i] = card;
                        state->freecells[f_slot] = 255;

                        // int f_slot = free_indices[i];
                        // uint8_t card = state->freecells[f_slot];
                        // state->columns[src][len - seq_len + i] = card; // Restore order
                        // state->freecells[f_slot] = 255;
                    }
                }
            }
        }

        // C) FreeCell -> Tableau
        // Rules:
        // - Not onto empty column if fits on other column.

        for (int f = 0; f < NUM_FREECELLS; f++)
        {
            if (state->freecells[f] == 255 || seqInFreecells(state, f))
                continue;

            uint8_t fc_card = state->freecells[f];
            int dst = fittingColumnDst(state, fc_card);
            if (dst != -1)
            {
                // Make the move
                state->freecells[f] = 255; // CLEAR!
                state->columns[dst][state->col_lens[dst]] = fc_card;
                state->col_lens[dst]++;

                move_history[depth] = (Move){MOVE_FREECELL_TO_TABLEAU, f, dst, fc_card, 0, *state};

                if (solve(state, depth + 1))
                    return true;

                // Backtrack
                state->col_lens[dst]--;
                state->columns[dst][state->col_lens[dst]] = 255; // CLEAR!
                state->freecells[f] = fc_card;                   // RESTORE
            }
        }
    }
    return false;
}

// Maximum total capacity for evacuating / breaking up a sequence (FreeCells + empty columns)
static inline int max_evacuable_cards(int free_cells, int empty_cols)
{
    if (empty_cols == 0)
        return free_cells;
    return ((free_cells + 1) * (1 << empty_cols) - 1) + free_cells;
}

// --- PRINT FUNCTIONS ---

void print_card(uint8_t card);

void skipInputLine()
{
    int c;
    while ((c = getchar()) != '\n' && c != EOF)
        ;
}

void print_solution(void)
{
    printf("\n====================================\n");
    printf(" SOLUTION FOUND IN %d MOVES:\n", total_solution_moves);
    printf("====================================\n\n");

    for (int i = 0; i < total_solution_moves; i++)
    {
        Move m = move_history[i];
        printf("Move %3d: ", i + 1);

        switch (m.type)
        {
        case MOVE_TABLEAU_TO_FOUNDATION:
            printf("Column %d   -> Foundation  [", m.src + 1);
            print_card(m.card);
            printf("]\n");
            break;
        case MOVE_FREECELL_TO_FOUNDATION:
            printf("FreeCell %d -> Foundation  [", m.src + 1);
            print_card(m.card);
            printf("]\n");
            break;
        case MOVE_TABLEAU_TO_TABLEAU:
            printf("Column %d   -> Column %d     [", m.src + 1, m.dst + 1);
            print_card(m.card);
            printf("]\n");
            break;
        case MOVE_TABLEAU_TO_FREECELL:
            printf("Column %d   -> FreeCell %d   [", m.src + 1, m.dst + 1);
            print_card(m.card);
            printf("]\n");
            break;
        case MOVE_FREECELL_TO_TABLEAU:
            printf("FreeCell %d -> Column %d     [", m.src + 1, m.dst + 1);
            print_card(m.card);
            printf("]\n");
            break;
        }

        print_game_state(&m.gameState);
        printf("Press Enter to continue ");
        fflush(stdout);
        skipInputLine();
    }
    printf("\n");
}

// Reads cards in the format "p k", "pk", "kr 10", "h,2", "k;a", and so on.
int parse_card(const char *suit_str, const char *rank_str, uint8_t *out_card)
{
    // 1. Determine the suit
    uint8_t suit = 255;
    if (strcmp(suit_str, "p") == 0)
        suit = 0; // Spades
    else if (strcmp(suit_str, "h") == 0)
        suit = 1; // Hearts
    else if (strcmp(suit_str, "k") == 0)
        suit = 2; // Diamonds
    else if (strcmp(suit_str, "kr") == 0)
        suit = 3; // Clubs
    else
        return -1;

    // 2. Determine the rank
    uint8_t rank = 0;
    if (strcmp(rank_str, "a") == 0)
        rank = 1;
    else if (strcmp(rank_str, "j") == 0)
        rank = 11;
    else if (strcmp(rank_str, "q") == 0)
        rank = 12;
    else if (strcmp(rank_str, "k") == 0)
        rank = 13;
    else
    {
        int r = atoi(rank_str);
        if (r >= 2 && r <= 10)
            rank = (uint8_t)r;
        else
            return -1;
    }

    *out_card = make_card(rank, suit);
    return 0;
}

bool validate_deck(const GameState *game)
{
    bool seen[52] = {false};
    int card_count = 0;

    // 1. Count and mark cards in the tableau
    for (int col = 0; col < NUM_COLUMNS; col++)
    {
        for (int i = 0; i < game->col_lens[col]; i++)
        {
            uint8_t card = game->columns[col][i];

            if (card >= 52)
            {
                printf("\nError: Invalid card value (%d) found!\n", card);
                return false;
            }

            if (seen[card])
            {
                printf("\nError: Card ");
                print_card(card);
                printf(" appears TWICE on the board!\n");
                return false;
            }

            seen[card] = true;
            card_count++;
        }
    }

    // 2. Check whether a card is missing
    if (card_count != 52)
    {
        printf("\nError: Only %d of 52 cards were read!\n", card_count);
        printf("The following cards are MISSING:\n");

        for (int i = 0; i < 52; i++)
        {
            if (!seen[i])
            {
                printf(" - ");
                print_card(i);
                printf("\n");
            }
        }
        return false;
    }

    printf("\n--> Validation successful: Exactly 52 unique cards were read!\n");
    return true;
}

bool parse_board_from_file(GameState *out_game, FILE *f)
{
    memset(out_game, 0, sizeof(GameState));
    memset(out_game->freecells, 255, 4);

    char line_buf[512];
    int current_col = 0;

    printf("--- Please enter the board (8 columns) ---\n");

    while (current_col < 8 && fgets(line_buf, sizeof(line_buf), f))
    {
        char *l = line_buf;
        while (isspace(*l))
            l++;

        if (*l == '\0' || *l == '#')
            continue;

        if (strncmp(l, "-", 1) == 0)
        {
            out_game->col_lens[current_col++] = 0;
            printf("Column %d read (0 cards - empty)\n", current_col);
            continue;
        }

        char *ptr = l;
        while (*ptr && out_game->col_lens[current_col] < 19)
        {
            // Skip whitespace, commas, and semicolons
            while (*ptr && (isspace(*ptr) || *ptr == ',' || *ptr == ';'))
                ptr++;
            if (*ptr == '\0')
                break;

            // Read the suit
            char suit_buf[8] = {0};
            int s_idx = 0;
            while (*ptr && isalpha(*ptr) && s_idx < 7)
            {
                suit_buf[s_idx++] = (char)tolower(*ptr++);
            }

            // Skip whitespace between suit and rank
            while (*ptr && isspace(*ptr))
                ptr++;

            // Read the rank
            char rank_buf[8] = {0};
            int r_idx = 0;
            while (*ptr && isalnum(*ptr) && r_idx < 7)
            {
                rank_buf[r_idx++] = (char)tolower(*ptr++);
            }

            if (s_idx == 0 || r_idx == 0)
            {
                printf("\nError: Incomplete card in column %d near '%s'\n", current_col + 1, ptr);
                return false;
            }

            uint8_t card;
            if (parse_card(suit_buf, rank_buf, &card) == 0)
            {
                uint8_t len = out_game->col_lens[current_col];
                out_game->columns[current_col][len] = card;
                out_game->col_lens[current_col]++;
            }
            else
            {
                printf("\nError: Invalid card '%s %s' in column %d!\n", suit_buf, rank_buf, current_col + 1);
                return false;
            }
        }

        printf("Column %d read (%d cards)\n", current_col + 1, out_game->col_lens[current_col]);
        current_col++;
    }

    if (current_col < 8)
    {
        printf("\nError: Only %d of 8 columns were read!\n", current_col);
        return false;
    }

    // Always check that the deck is complete (exactly 52 unique cards)!
    return validate_deck(out_game);
}

void print_card(uint8_t card)
{

    if (card == 255)
    {
        printf("----");
        return;
    }
    uint8_t suit = card & 3;
    uint8_t rank = card >> 2;
    if (suit == 1 || suit == 2)
    {
        printf("%s", ANSI_ROT);
    }
    printf("%s %s", suits[suit], ranks[rank]);
    if (suit == 1 || suit == 2)
    {
        printf("%s", ANSI_RESET);
    }
}

void print_game_state(const GameState *s)
{
    printf("\n===================================== CURRENT STATE =====================================\n");

    // 1. Foundations & FreeCells
    printf("FreeCells:   ");
    for (int f = 0; f < NUM_FREECELLS; f++)
    {
        printf("[");
        print_card(s->freecells[f]);
        printf("] ");
    }
    printf("      Foundations: ");
    // const char *suits[] = {"Spades", "Hearts", "Diamonds", "Clubs"};
    for (int i = 0; i < 4; i++)
    {
        if (s->foundations[i] == 0)
        {
            if (i == 1 || i == 2)
            {
                printf(ANSI_ROT);
            }
            printf("[%s --] ", suits[i]);
            if (i == 1 || i == 2)
            {
                printf(ANSI_RESET);
            }
        }
        else
        {
            uint8_t card = make_card(s->foundations[i], i);
            printf("[");
            print_card(card);
            printf("] ");
        }
    }

    printf("\n-----------------------------------------------------------------------------------------\n");

    // 2. Determine the maximum tableau height
    int max_len = 0;
    for (int col = 0; col < NUM_COLUMNS; col++)
    {
        if (s->col_lens[col] > max_len)
            max_len = s->col_lens[col];
    }

    // Column headers (exactly 12 characters wide per column)
    for (int col = 0; col < NUM_COLUMNS; col++)
    {
        char header[16];
        snprintf(header, sizeof(header), "Column %d", col + 1);
        printf("%-10s", header);
    }
    printf("\n");

    // Print the tableau row by row, top to bottom
    for (int row = 0; row < max_len; row++)
    {
        for (int col = 0; col < NUM_COLUMNS; col++)
        {
            if (row < s->col_lens[col])
            {
                uint8_t card = s->columns[col][row];

                // Format the card into a string first
                // Scratch buffer for a print_card equivalent:
                // const char *suit_names[] = {"Spades", "Hearts", "Diamonds", "Clubs"};
                // war nur zum Debuggen:
                // const char *rank_names[] = {"--", "A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"};

                // war nur zum Debuggen:
                // uint8_t suit = card & 3;
                // uint8_t rank = (card >> 2) + 1;

                print_card(card);
                printf("      ");
            }
            else
            {
                printf("%-10s", ""); // Empty cell
            }
        }
        printf("\n");
    }
    printf("=========================================================================================\n\n");
}

static void print_usage(FILE *out, const char *prog)
{
    fprintf(out,
            "Usage: %s [OPTION] [FILE]\n"
            "\n"
            "Solver for Baker's Game.\n"
            "\n"
            "Reads a board with 8 columns. Without FILE, input is read from standard input.\n"
            "FILE is used only if it is a regular file; otherwise stdin is read.\n"
            "\n"
            "Options:\n"
            "  -h, -?, --help    display this help and exit\n"
            "\n"
            "Board:\n"
            "  One line per column. Cards for example as \"p k\", \"h,2\", \"kr 10\".\n"
            "  Suits: p (spades), h (hearts), k (diamonds), kr (clubs).\n"
            "  Ranks: a, 2-10, j, q, k. A line \"-\" is an empty column.\n"
            "  Lines starting with # are ignored.\n",
            prog);
}

int main(int argc, char **argv)
{
    const char *prog = (argc > 0 && argv[0] && argv[0][0]) ? argv[0] : "main3";

    if (argc >= 2 &&
        (strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "-?") == 0 || strcmp(argv[1], "--help") == 0))
    {
        print_usage(stdout, prog);
        return 0;
    }

    arena_buffer = calloc(ARENA_SIZE, 1);
    hash_buckets = calloc(HASH_TABLE_SIZE, sizeof(uint32_t));

    if (!arena_buffer || !hash_buckets)
    {
        fprintf(stderr, "Could not allocate memory.\n");
        return 1;
    }

    GameState game;
    FILE *input = stdin;
    bool close_input = false;

    if (argc == 2)
    {
        struct stat st;
        if (stat(argv[1], &st) == 0 && S_ISREG(st.st_mode))
        {
            input = fopen(argv[1], "r");
            if (!input)
            {
                fprintf(stderr, "Could not open file '%s'.\n", argv[1]);
                free(arena_buffer);
                free(hash_buckets);
                return 1;
            }
            close_input = true;
        }
    }

    if (!parse_board_from_file(&game, input))
    {
        fprintf(stderr, "\nError while reading input! Aborting.\n");
        if (close_input)
            fclose(input);
        free(arena_buffer);
        free(hash_buckets);
        return 1;
    }

    if (close_input)
        fclose(input);

    printf("\nSearching for a solution for the loaded board...\n");
    print_game_state(&game);

    if (solve(&game, 0))
    {
        print_solution();
        printf("Unique states in RAM: %zu bytes used in the arena.\n", arena_offset);
    }
    else
    {
        printf("No solution found.\n");
    }

    printf("Unique states in RAM: %zu bytes used in the arena.\n", arena_offset);
    printf("steps %" PRIu64 "\n", steps);

    free(arena_buffer);
    free(hash_buckets);
    return 0;
}
