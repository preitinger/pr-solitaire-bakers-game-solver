#define _GNU_SOURCE
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdarg.h>

#define ARENA_SIZE (256ULL * 1024 * 1024 << 2) // 256 MB Hauptspeicher für Zustände
// ~67 Millionen Buckets (braucht nur ca. 268 MB RAM for hash_buckets)
#define HASH_TABLE_SIZE 67108859 // Primzahl
// #define HASH_TABLE_SIZE 8388607             // Primzahl für Open-Addressing
// #define MAX_DEPTH 200
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

// --- TYPEN & STRUKTUREN ---

// Farben: 0 = Pik, 1 = Herz, 2 = Karo, 3 = Kreuz
// Rang:   0 (Ass) bis 12 (König)
// Formel: Karte = (Rang * 4) + Farbe (0..51, 255 = leer)

typedef struct
{
    uint8_t columns[NUM_COLUMNS][19];
    uint8_t col_lens[NUM_COLUMNS];
    uint8_t freecells[NUM_FREECELLS]; // 255 = Leer
    uint8_t foundations[4];           // Höchster gelöster Rang (0 = Kein, 1 = Ass, ..., 13 = König)
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
    uint8_t count; // NEU: Anzahl bewegter Karten (für Meta-Moves)
    GameState gameState;
} Move;

// --- GLOBALE SPEICHERSYSTEME ---

static uint8_t *arena_buffer = NULL;
static size_t arena_offset = 0;
static uint32_t *hash_buckets = NULL;

static Move move_history[MAX_DEPTH];
static int total_solution_moves = 0;
static uint64_t steps = 0;

const char *suits[] = {"♠", "♥", "♦", "♣"};
const char *ranks[] = {" A", " 2", " 3", " 4", " 5", " 6", " 7", " 8", " 9", "10", " J", " Q", " K"};

// --- ARITHMETIK & HELFER ---

uint8_t make_card(uint8_t rank_1_to_13, uint8_t suit_0_to_3)
{
    return ((rank_1_to_13 - 1) << 2) | (suit_0_to_3 & 3);
}

// --- KANONISCHES PACKEN & HASH-SET ---

int compColumn(const void* a1, const void* b1, void* s1) {
    const int* a = (const int*) a1;
    const int* b = (const int*) b1;
    const GameState* s = (const GameState*) s1;
    // 1. Leere Spalten zuerst
    // 2. Dann 1. Karte vergleichen

    bool emptyA = s->col_lens[*a] == 0;
    bool emptyB = s->col_lens[*b] == 0;

    if (emptyA) {
        if (emptyB) {
            return 0;
        } else {
            return -1;
        }
    } else {
        if (emptyB) {
            return 1;
        } else {
            return (int) s->columns[*a][0] - (int) s->columns[*b][0];
        }
    }
}

int pack_state(const GameState *s, uint8_t *buf)
{
    int idx = 0;

    // 1. Foundations (4 Bytes)
    for (int i = 0; i < 4; i++)
        buf[idx++] = s->foundations[i];

    // 2. FreeCells sortieren (Symmetriebrechung) & packen (NUM_FREECELLS Bytes)
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

    // 3. Tableau-Spalten sortieren
    int sorted[NUM_COLUMNS];
    for (int i = 0; i < NUM_COLUMNS; ++i) {
        sorted[i] = i;
    }
    qsort_r(sorted, NUM_COLUMNS, sizeof(int), &compColumn, (void*)s);

    // TODO permutate sorted so that columns are sorted

    // 3. Tableau-Spalten
    for (int colI = 0; colI < NUM_COLUMNS; colI++)
    {
        int col = sorted[colI];
        buf[idx++] = s->col_lens[col];
        for (int i = 0; i < s->col_lens[col]; i++)
        {
            buf[idx++] = s->columns[col][i];
        }
    }

    return idx; // Exakte Gesamtlänge
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
        printf("\n>>> SNAPSHOT nach %llu Zuständen (Arena: %.2f MB) <<<\n",
               (unsigned long long)(steps),
               arena_offset / (1024.0 * 1024.0));
        print_game_state(state);
    }

    uint8_t tmp_buf[64];
    int len = pack_state(state, tmp_buf);

    uint32_t hash = hash_bytes(tmp_buf, len);
    uint32_t index = hash % HASH_TABLE_SIZE;
    uint32_t probes = 0;

    // Suchen nach freiem Slot ODER gewähltem Zustand
    while (hash_buckets[index] != 0)
    {
        uint32_t existing_offset = hash_buckets[index] - 1;
        uint8_t *existing_data = &arena_buffer[existing_offset];

        if (memcmp(existing_data, tmp_buf, len) == 0)
        {
            return true; // Bereits besucht!
        }

        index = (index + 1) % HASH_TABLE_SIZE;
        probes++;

        // DER PROBES-GUARD (Verhindert das Hängenbleiben!):
        if (probes >= HASH_TABLE_SIZE)
        {
            fprintf(stderr, "\n[FEHLER] Hash-Tabelle ist voll (%d Buckets)! Bitte HASH_TABLE_SIZE vergrößern.\n", HASH_TABLE_SIZE);
            exit(1);
        }
    }

    if (probes > maxProbes)
    {
        maxProbes = probes;
        printf("maxProbes: %d - steps: %llu\n", maxProbes, steps);
    }

    // Neu -> In die Arena schreiben
    if (arena_offset + len > ARENA_SIZE)
    {
        fprintf(stderr, "\n[FEHLER] Arena-Speicher voll!\n");
        exit(1);
    }

    uint32_t new_offset = (uint32_t)arena_offset;
    *arenaIndex = new_offset;
    memcpy(&arena_buffer[new_offset], tmp_buf, len);
    hash_buckets[index] = new_offset + 1; // 1-basierter Offset
    arena_offset += len;

    return false; // Zustand war neu
}
// --- CORE REKURSION & LOGIK ---

bool is_solved(const GameState *state)
{
    return state->foundations[0] == 13 && state->foundations[1] == 13 &&
           state->foundations[2] == 13 && state->foundations[3] == 13;
}

// Berechnet wie viele Karten auf einmal bewegt werden dürfen
int max_movable_cards(int free_cells, int empty_cols, bool dst_is_empty)
{
    if (dst_is_empty)
    {
        // Wenn das Ziel leer ist, steht diese Spalte nicht als Zwischenspeicher zur Verfügung
        if (empty_cols == 0)
            return free_cells + 1;
        return (free_cells + 1) * (1 << (empty_cols - 1));
    }
    else
    {
        return (free_cells + 1) * (1 << empty_cols);
    }
}

// Gibt die Länge der validen Sequenz am Ende von col zurück (mindestens 1)
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

        // Bäckers Spiel: Gleicher Suit und exakt Rang - 1
        if (suit_below == suit_above && rank_below + 1 == rank_above)
        {
            seq_len++;
        }
        else
        {
            break; // Sequenz unterbrochen
        }
    }
    return seq_len;
}

// // Berechnet, wie viele Sequenzkarten insgesamt aus einer Spalte
// // auf andere Spalten/FreeCells verteilt werden können, um die Karte darunter freizulegen.
// int max_evacuable_cards(int free_cells, int empty_cols) {
//     if (empty_cols == 0) {
//         // Ohne leere Spalten können wir nur so viele Karten wegbewegen,
//         // wie wir FreeCells haben (plus evtl. Anbauen an bestehende Spalten).
//         return free_cells;
//     }
//     // (F + 1) * 2^E - 1 ist die max. Blockgröße auf leere Spalten,
//     // zusätzlich können F Karten auf FreeCells parken.
//     return ((free_cells + 1) * (1 << empty_cols) - 1) + free_cells;
// }

bool seqInFreecells(GameState *state, int freecell)
{
    // Ist die nächsthöhere Karte der gleichen Farbe wie die Karte in `freecell` in einer anderen freecell oder oberste erreichbare Karte in einer Spalte?
    // Dann nämlich sollte eher die höchste gespielt werden, jedoch keinesfalls diese.
    int card = state->freecells[freecell];
    if (card < 52)
    {
        int nextCard = card + 4;
        if (nextCard < 52)
        {
            for (int f = 0; f < 4; ++f)
            {
                if (state->freecells[f] == nextCard)
                {
                    return true;
                }
            }

            // Das ist Unsinn:
            // for (int c = 0; c < NUM_COLUMNS; ++c)
            // {
            //     if (state->col_lens[c] > 0 && state->columns[c][state->col_lens[c] - 1] == nextCard)
            //     {
            //         return true;
            //     }
            // }
        }
    }

    return false;
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
        printf("\n\nMAX DEPTH - breche ab!\n\n");
        return false;
    }

    // Prüfen, ob dieser Zustand bereits in der Arena/Hash-Tabelle liegt
    uint32_t arenaIndex = -1;
    if (is_visited_or_add(state, &arenaIndex))
        return false;

    // =========================================================================
    // 1. AUTO-MOVES (DOMINANZ-REGEL FOR BÄCKERS SPIEL)
    // =========================================================================

    // Auto-Move: Tableau -> Foundation
    for (int col = 0; col < 8; col++)
    {
        if (state->col_lens[col] > 0)
        {
            uint8_t card = state->columns[col][state->col_lens[col] - 1];
            uint8_t suit = card & 3;
            uint8_t rank = (card >> 2) + 1;

            if (rank == state->foundations[suit] + 1)
            {
                // Zug ausführen & Speicherplatz leeren
                state->foundations[suit]++;
                state->col_lens[col]--;
                state->columns[col][state->col_lens[col]] = 255; // LEEREN!

                move_history[depth] = (Move){MOVE_TABLEAU_TO_FOUNDATION, col, suit, card, 0, *state};

                bool res = solve(state, depth + 1);

                // Backtrack
                state->columns[col][state->col_lens[col]] = card; // WIEDERHERSTELLEN
                state->col_lens[col]++;
                state->foundations[suit]--;

                return res; // HARTER CUTOFF!
            }
        }
    }

    // Auto-Move: FreeCell -> Foundation
    for (int f = 0; f < 4; f++)
    {
        if (state->freecells[f] != 255)
        {
            uint8_t card = state->freecells[f];
            uint8_t suit = card & 3;
            uint8_t rank = (card >> 2) + 1;

            if (rank == state->foundations[suit] + 1)
            {
                // Zug ausführen
                state->foundations[suit]++;
                state->freecells[f] = 255; // LEEREN!

                move_history[depth] = (Move){MOVE_FREECELL_TO_FOUNDATION, f, suit, card, 0, *state};

                bool res = solve(state, depth + 1);

                // Backtrack
                state->freecells[f] = card; // WIEDERHERSTELLEN
                state->foundations[suit]--;

                return res; // HARTER CUTOFF!
            }
        }
    }

    // // ALT BEGIN
    // // =========================================================================
    // // 2. NORMALES BACKTRACKING (TABLEAU UND FREECELLS)
    // // =========================================================================

    // // A) Tableau -> Tableau
    // for (int src = 0; src < 8; src++)
    // {
    //     if (state->col_lens[src] == 0)
    //         continue;

    //     uint8_t src_card = state->columns[src][state->col_lens[src] - 1];

    //     for (int dst = 0; dst < 8; dst++)
    //     {
    //         if (src == dst)
    //             continue;

    //         bool valid = false;
    //         if (state->col_lens[dst] == 0)
    //         {
    //             // Nur sinnvoll, wenn wir damit wirklich Karten freilegen
    //             if (state->col_lens[src] > 1)
    //                 valid = true;
    //         }
    //         else
    //         {
    //             uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
    //             // Bäckers Spiel: Gleiche Farbe, Rang - 1
    //             if ((src_card + 4) == dst_card)
    //                 valid = true;
    //         }

    //         if (valid)
    //         {
    //             // Zug ausführen
    //             state->col_lens[src]--;
    //             state->columns[src][state->col_lens[src]] = 255; // LEEREN!

    //             state->columns[dst][state->col_lens[dst]] = src_card;
    //             state->col_lens[dst]++;

    //             move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, src, dst, src_card};

    //             if (solve(state, depth + 1))
    //                 return true;

    //             // Backtrack
    //             state->col_lens[dst]--;
    //             state->columns[dst][state->col_lens[dst]] = 255; // LEEREN!

    //             state->columns[src][state->col_lens[src]] = src_card; // WIEDERHERSTELLEN
    //             state->col_lens[src]++;
    //         }
    //     }
    // }

    // =========================================================================
    // 2. NORMALES BACKTRACKING (TABLEAU UND FREECELLS)
    // =========================================================================

    // A) Tableau -> Tableau (INKLUSIVE META-MOVES / SUPERMOVES)
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

            // Länge der zusammenhängenden Sequenz am Ende von src
            int seq_len = get_sequence_length(state, src);

            for (int dst = 0; dst < NUM_COLUMNS; dst++)
            {
                if (src == dst)
                    continue;

                bool dst_is_empty = (state->col_lens[dst] == 0);

                // Maximale Kapazität berechnen
                int current_empty_cols = empty_cols_count - (dst_is_empty ? 1 : 0);
                int max_cards = max_movable_cards(free_cells_count, current_empty_cols, dst_is_empty);

                if (dst_is_empty)
                {
                    // ZIELSPALTE IS LEER:
                    // Nur verschieben, wenn:
                    // 1. Die Sequenz nicht bereits die GESAMTE Spalte ist (Sinnloser ISOMORPHIE-Zug).
                    // 2. Die Sequenz innerhalb des Max-Movable-Limits liegt.
                    // NEU
                    // 3. Die nächsthöhere Karte nach der höchsten der bewegten Sequenz nicht auch erreichbar ist.
                    if (seq_len < state->col_lens[src] && seq_len <= max_cards)
                    {
                        int k = seq_len;
                        uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

                        // --- ZUG AUSFÜHREN ---
                        int src_start = state->col_lens[src] - k;
                        for (int i = 0; i < k; i++)
                        {
                            state->columns[dst][i] = state->columns[src][src_start + i];
                            state->columns[src][src_start + i] = 255;
                        }
                        state->col_lens[src] -= k;
                        state->col_lens[dst] = k;

                        move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k, *state};

                        if (solve(state, depth + 1))
                            return true;

                        // --- BACKTRACK ---
                        state->col_lens[src] += k;
                        state->col_lens[dst] = 0;
                        for (int i = 0; i < k; i++)
                        {
                            state->columns[src][src_start + i] = state->columns[dst][i];
                            state->columns[dst][i] = 255;
                        }
                    }
                }
                else
                {
                    // ZIELSPALTE IST NICHT LEER:
                    uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];

                    // Wir suchen in der Quell-Sequenz (von 1 bis min(seq_len, max_cards))
                    // nach der EINZIGEN Karte, die auf dst_card passt!
                    int movable_limit = min(seq_len, max_cards);

                    for (int k = 1; k <= movable_limit; k++)
                    {
                        uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

                        // Regel für Bäckers Spiel: Gleiche Farbe (gleiches Symbol), Rang genau 1 niedriger.
                        // (top_card_of_group + 4) == dst_card
                        if ((top_card_of_group + 4) == dst_card)
                        {
                            // printf("Vor dem Zug\n");
                            // print_game_state(state);
                            // --- ZUG AUSFÜHREN ---
                            int src_start = state->col_lens[src] - k;
                            for (int i = 0; i < k; i++)
                            {
                                state->columns[dst][state->col_lens[dst] + i] = state->columns[src][src_start + i];
                                state->columns[src][src_start + i] = 255;
                            }
                            state->col_lens[src] -= k;
                            state->col_lens[dst] += k;

                            move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k, *state};

                            // printf("Nach dem Zug\n");
                            // print_game_state(state);
                            if (solve(state, depth + 1))
                            {
                                return true;
                            }

                            // printf("Vor Backtrack\n");
                            // print_game_state(state);

                            // --- BACKTRACK ---
                            state->col_lens[dst] -= k;
                            state->col_lens[src] += k;
                            for (int i = 0; i < k; i++)
                            {
                                state->columns[src][src_start + i] = state->columns[dst][state->col_lens[dst] + i];
                                state->columns[dst][state->col_lens[dst] + i] = 255;
                            }

                            // Da jede Karte im Spiel einmalig ist, kann nur EIN k passen.
                            // Nach dem Match und Backtrack abbrechen!

                            // printf("Nach Backtrack\n");
                            // print_game_state(state);
                            break;
                        }
                    }
                }
            }
        }
    }
    // // A) Tableau -> Tableau (INKLUSIVE META-MOVES / SUPERMOVES)

    // // Vorab-Berechnung der freien Ressourcen für die Formel
    // int free_cells_count = 0;
    // for (int f = 0; f < NUM_FREECELLS; f++)
    // {
    //     if (state->freecells[f] == 255)
    //         free_cells_count++;
    // }

    // int empty_cols_count = 0;
    // for (int c = 0; c < NUM_COLUMNS; c++)
    // {
    //     if (state->col_lens[c] == 0)
    //         empty_cols_count++;
    // }

    // for (int src = 0; src < NUM_COLUMNS; src++)
    // {
    //     if (state->col_lens[src] == 0)
    //         continue;

    //     // Wie viele zusammenhängende Karten liegen am Ende von src?
    //     int seq_len = get_sequence_length(state, src);

    //     for (int dst = 0; dst < NUM_COLUMNS; dst++)
    //     {
    //         if (src == dst)
    //             continue;

    //         bool dst_is_empty = (state->col_lens[dst] == 0);

    //         // Korrektur: Wenn die Zielspalte leer ist, zählt sie nicht als freie Spalte für den Transfer
    //         int current_empty_cols = empty_cols_count - (dst_is_empty ? 1 : 0);
    //         int max_cards = max_movable_cards(free_cells_count, current_empty_cols, dst_is_empty);

    //         int movable = min(seq_len, max_cards);

    //         // Alle möglichen Sequenz-Längen ausprobieren (von 1 bis movable)
    //         for (int k = 1; k <= movable; k++)
    //         {
    //             uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

    //             bool valid = false;
    //             if (dst_is_empty)
    //             {
    //                 // Das Verschieben einer kompletten Spalte auf eine leere Spalte bringt keinen Nutzen
    //                 if (k < state->col_lens[src])
    //                     valid = true;
    //             }
    //             else
    //             {
    //                 uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
    //                 // Bäckers Spiel: Gleiche Farbe, Rang - 1
    //                 if ((top_card_of_group + 4) == dst_card)
    //                     valid = true;
    //             }

    //             if (valid)
    //             {
    //                 // --- ZUG AUSFÜHREN (k Karten von src nach dst) ---
    //                 int src_start = state->col_lens[src] - k;

    //                 for (int i = 0; i < k; i++)
    //                 {
    //                     uint8_t card = state->columns[src][src_start + i];
    //                     state->columns[dst][state->col_lens[dst] + i] = card;
    //                     state->columns[src][src_start + i] = 255; // LEEREN
    //                 }

    //                 state->col_lens[src] -= k;
    //                 state->col_lens[dst] += k;

    //                 move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k};

    //                 if (solve(state, depth + 1))
    //                     return true;

    //                 // --- BACKTRACK (k Karten zurückstellen) ---
    //                 state->col_lens[src] += k;
    //                 state->col_lens[dst] -= k;

    //                 for (int i = 0; i < k; i++)
    //                 {
    //                     uint8_t card = state->columns[dst][state->col_lens[dst] + i];
    //                     state->columns[src][src_start + i] = card;
    //                     state->columns[dst][state->col_lens[dst] + i] = 255; // LEEREN
    //                 }
    //             }
    //         }
    //     }
    // }

    // B) Tableau -> FreeCells (ATOMARER META-MOVE & EINZELZÜGE)

    {
        // Freie FreeCells zählen und Indizes sammeln
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

                // FALL 1: Einzelkarte (seq_len == 1) auf eine FreeCell legen
                if (seq_len == 1)
                {
                    int f_slot = free_indices[0];
                    uint8_t card = state->columns[src][len - 1];
                    const char *suit = suits[card & 3];
                    const char *rank = ranks[card >> 2];

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
                // FALL 2: Atomarer Meta-Move – Eine GESAMTE Sequenz auf FreeCells evakuieren
                else if (seq_len > 1 && seq_len <= free_cells_count && len > seq_len)
                {
                    // Wir legen ALLE seq_len Karten der Sequenz auf einmal auf FreeCells,
                    // um die Nicht-Sequenz-Karte DARUNTER freizulegen.
                    uint8_t card;
                    // ZUG AUSFÜHREN
                    for (int i = 0; i < seq_len; i++)
                    {
                        card = state->columns[src][len - 1 - i];
                        int f_slot = free_indices[i];
                        state->freecells[f_slot] = card;
                        state->columns[src][len - 1 - i] = 255;
                    }
                    state->col_lens[src] -= seq_len;

                    // In der Historie vermerken (z. B. count = seq_len)
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
                        // state->columns[src][len - seq_len + i] = card; // Reihenfolge wiederherstellen
                        // state->freecells[f_slot] = 255;
                    }
                }
            }
        }

        // B) FreeCell -> Tableau
        // TODO Neue Regel: Wenn eine Sequenz in den Freecells ist, immer nur den höchsten auf eine freie Spalte bewegen!
        // spiele/06.txt ohne diese neue Regel: Lösung mit 113 Zügen,
        // ohne? -- ebenfalls 113 lol

        for (int f = 0; f < 4; f++)
        {
            if (state->freecells[f] == 255 || seqInFreecells(state, f))
                continue;

            uint8_t fc_card = state->freecells[f];

            for (int dst = 0; dst < 8; dst++)
            {
                bool valid = false;
                if (state->col_lens[dst] == 0)
                {
                    valid = true;
                }
                else
                {
                    uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
                    if ((fc_card + 4) == dst_card)
                        valid = true;
                }

                if (valid)
                {
                    // Zug ausführen
                    state->freecells[f] = 255; // LEEREN!
                    state->columns[dst][state->col_lens[dst]] = fc_card;
                    state->col_lens[dst]++;

                    move_history[depth] = (Move){MOVE_FREECELL_TO_TABLEAU, f, dst, fc_card, 0, *state};

                    if (solve(state, depth + 1))
                        return true;

                    // Backtrack
                    state->col_lens[dst]--;
                    state->columns[dst][state->col_lens[dst]] = 255; // LEEREN!
                    state->freecells[f] = fc_card;                   // WIEDERHERSTELLEN
                }
            }
        }

        // // C) Tableau -> FreeCell
        // for (int src = 0; src < 8; src++)
        // {
        //     if (state->col_lens[src] == 0)
        //         continue;

        //     for (int f = 0; f < 4; f++)
        //     {
        //         if (state->freecells[f] == 255)
        //         {
        //             uint8_t card = state->columns[src][state->col_lens[src] - 1];

        //             // Zug ausführen
        //             state->col_lens[src]--;
        //             state->columns[src][state->col_lens[src]] = 255; // LEEREN!
        //             state->freecells[f] = card;

        //             move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, src, f, card, 0, *state};

        //             if (solve(state, depth + 1))
        //                 return true;

        //             // Backtrack
        //             state->freecells[f] = 255;                        // LEEREN!
        //             state->columns[src][state->col_lens[src]] = card; // WIEDERHERSTELLEN
        //             state->col_lens[src]++;

        //             break; // Erste freie Cell nutzen reicht
        //         }
        //     }
        // }
    }
    return false;
}

// // --- HILFSFUNKTIONEN (Sollten bei dir bereits existieren) ---

// // Berechnet die maximale Anzahl an Karten, die auf EINE Zielspalte bewegt werden können
// static inline int max_movable_cards(int free_cells, int empty_cols, bool dst_is_empty) {
//     int E = empty_cols; // Bereit korrigiert um die Zielspalte falls nötig
//     return (free_cells + 1) * (1 << E);
// }

// // Berechnet, wie viele Sequenzkarten insgesamt evakuiert werden können
// static inline int max_evacuable_cards(int free_cells, int empty_cols) {
//     if (empty_cols == 0) return free_cells;
//     return ((free_cells + 1) * (1 << empty_cols) - 1) + free_cells;
// }

// // --- DIE VOLLSTÄNDIGE SOLVE-FUNKTION ---

// bool solve(GameState *state, int depth)
// {
//     if (depth >= MAX_DEPTH)
//         return false;

//     // Prüfen, ob das Spiel gewonnen ist (alle Foundations voll = 52 Karten)
//     int total_foundations = 0;
//     for (int f = 0; f < NUM_FOUNDATIONS; f++) {
//         if (state->foundations[f] != 255) {
//             total_foundations += (state->foundations[f] % 13) + 1;
//         }
//     }
//     if (total_foundations == 52)
//         return true;

//     // =========================================================================
//     // 1. AUTO-MOVES / FOUNDATION MOVES (Priorität 1)
//     // =========================================================================

//     // A) Tableau -> Foundation
//     for (int src = 0; src < NUM_COLUMNS; src++)
//     {
//         int len = state->col_lens[src];
//         if (len == 0) continue;

//         uint8_t card = state->columns[src][len - 1];
//         uint8_t suit = card / 13;
//         uint8_t rank = card % 13;

//         uint8_t f_card = state->foundations[suit];
//         int required_rank = (f_card == 255) ? 0 : (f_card % 13) + 1;

//         if (rank == required_rank)
//         {
//             // Zug ausführen
//             state->foundations[suit] = card;
//             state->columns[src][len - 1] = 255;
//             state->col_lens[src]--;

//             move_history[depth] = (Move){MOVE_TABLEAU_TO_FOUNDATION, (uint8_t)src, suit, card, 1};

//             if (solve(state, depth + 1)) return true;

//             // Backtrack
//             state->col_lens[src]++;
//             state->columns[src][len - 1] = card;
//             state->foundations[suit] = (f_card == 255) ? 255 : (f_card);

//             // Safe-Move-Pruning: Wenn eine Karte gefahrlos auf die Foundation kann,
//             // müssen wir in diesem Zustand keine schlechteren Alternativen testen.
//             return false;
//         }
//     }

//     // B) FreeCell -> Foundation
//     for (int f = 0; f < NUM_FREECELLS; f++)
//     {
//         if (state->freecells[f] == 255) continue;

//         uint8_t card = state->freecells[f];
//         uint8_t suit = card / 13;
//         uint8_t rank = card % 13;

//         uint8_t f_card = state->foundations[suit];
//         int required_rank = (f_card == 255) ? 0 : (f_card % 13) + 1;

//         if (rank == required_rank)
//         {
//             // Zug ausführen
//             state->foundations[suit] = card;
//             state->freecells[f] = 255;

//             move_history[depth] = (Move){MOVE_FREECELL_TO_FOUNDATION, (uint8_t)f, suit, card, 1};

//             if (solve(state, depth + 1)) return true;

//             // Backtrack
//             state->freecells[f] = card;
//             state->foundations[suit] = f_card;

//             return false;
//         }
//     }

//     // Vorab-Berechnung freier Ressourcen für Backtracking
//     int free_cells_count = 0;
//     int free_indices[NUM_FREECELLS];
//     for (int f = 0; f < NUM_FREECELLS; f++) {
//         if (state->freecells[f] == 255) {
//             free_indices[free_cells_count++] = f;
//         }
//     }

//     int empty_cols_count = 0;
//     for (int c = 0; c < NUM_COLUMNS; c++) {
//         if (state->col_lens[c] == 0) empty_cols_count++;
//     }

//     // =========================================================================
//     // 2. BACKTRACKING: TABLEAU -> TABLEAU (META-MOVES)
//     // =========================================================================
//     for (int src = 0; src < NUM_COLUMNS; src++)
//     {
//         if (state->col_lens[src] == 0) continue;

//         int seq_len = get_sequence_length(state, src);

//         for (int dst = 0; dst < NUM_COLUMNS; dst++)
//         {
//             if (src == dst) continue;

//             bool dst_is_empty = (state->col_lens[dst] == 0);

//             int current_empty_cols = empty_cols_count - (dst_is_empty ? 1 : 0);
//             int max_cards = max_movable_cards(free_cells_count, current_empty_cols, dst_is_empty);

//             if (dst_is_empty)
//             {
//                 // ZIELSPALTE IST LEER:
//                 // Nur die GANZE Sequenz verschieben, niemals zerreißen!
//                 // Nicht verschieben, wenn die Sequenz bereits die komplette Spalte ist (Isomorphie).
//                 if (seq_len < state->col_lens[src] && seq_len <= max_cards)
//                 {
//                     int k = seq_len;
//                     uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

//                     // Zug ausführen
//                     int src_start = state->col_lens[src] - k;
//                     for (int i = 0; i < k; i++) {
//                         state->columns[dst][i] = state->columns[src][src_start + i];
//                         state->columns[src][src_start + i] = 255;
//                     }
//                     state->col_lens[src] -= k;
//                     state->col_lens[dst] = k;

//                     move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k};

//                     if (solve(state, depth + 1)) return true;

//                     // Backtrack
//                     state->col_lens[src] += k;
//                     state->col_lens[dst] = 0;
//                     for (int i = 0; i < k; i++) {
//                         state->columns[src][src_start + i] = state->columns[dst][i];
//                         state->columns[dst][i] = 255;
//                     }
//                 }
//             }
//             else
//             {
//                 // ZIELSPALTE IST NICHT LEER:
//                 uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
//                 int movable_limit = (seq_len < max_cards) ? seq_len : max_cards;

//                 for (int k = 1; k <= movable_limit; k++)
//                 {
//                     uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

//                     // Bäckers Spiel: Gleiche Farbe, Rang - 1
//                     if ((top_card_of_group + 4) == dst_card)
//                     {
//                         // Zug ausführen
//                         int src_start = state->col_lens[src] - k;
//                         for (int i = 0; i < k; i++) {
//                             state->columns[dst][state->col_lens[dst] + i] = state->columns[src][src_start + i];
//                             state->columns[src][src_start + i] = 255;
//                         }
//                         state->col_lens[src] -= k;
//                         state->col_lens[dst] += k;

//                         move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k};

//                         if (solve(state, depth + 1)) return true;

//                         // Backtrack
//                         state->col_lens[src] += k;
//                         state->col_lens[dst] -= k;
//                         for (int i = 0; i < k; i++) {
//                             state->columns[src][src_start + i] = state->columns[dst][state->col_lens[dst] + i];
//                             state->columns[dst][state->col_lens[dst] + i] = 255;
//                         }

//                         break; // Nur EIN k kann farblich passen
//                     }
//                 }
//             }
//         }
//     }

//     // =========================================================================
//     // 3. BACKTRACKING: FREECELL -> TABLEAU
//     // =========================================================================
//     for (int f = 0; f < NUM_FREECELLS; f++)
//     {
//         if (state->freecells[f] == 255) continue;

//         uint8_t card = state->freecells[f];

//         for (int dst = 0; dst < NUM_COLUMNS; dst++)
//         {
//             bool dst_is_empty = (state->col_lens[dst] == 0);

//             bool valid = false;
//             if (dst_is_empty)
//             {
//                 // Eine Karte von FreeCell auf eine leere Spalte legen
//                 valid = true;
//             }
//             else
//             {
//                 uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
//                 if ((card + 4) == dst_card) {
//                     valid = true;
//                 }
//             }

//             if (valid)
//             {
//                 // Zug ausführen
//                 state->columns[dst][state->col_lens[dst]] = card;
//                 state->col_lens[dst]++;
//                 state->freecells[f] = 255;

//                 move_history[depth] = (Move){MOVE_FREECELL_TO_TABLEAU, (uint8_t)f, (uint8_t)dst, card, 1};

//                 if (solve(state, depth + 1)) return true;

//                 // Backtrack
//                 state->freecells[f] = card;
//                 state->col_lens[dst]--;
//                 state->columns[dst][state->col_lens[dst]] = 255;
//             }
//         }
//     }

//     // =========================================================================
//     // 4. BACKTRACKING: TABLEAU -> FREECELLS (EINZEL- & ATOMARE META-MOVES)
//     // =========================================================================
//     if (free_cells_count > 0)
//     {
//         for (int src = 0; src < NUM_COLUMNS; src++)
//         {
//             int len = state->col_lens[src];
//             if (len == 0) continue;

//             int seq_len = get_sequence_length(state, src);

//             // FALL 1: Einzelne Karte am Ende (keine Sequenz mit Karte darüber)
//             if (seq_len == 1)
//             {
//                 int f_slot = free_indices[0]; // Erste freie FreeCell
//                 uint8_t card = state->columns[src][len - 1];

//                 // Zug ausführen
//                 state->freecells[f_slot] = card;
//                 state->columns[src][len - 1] = 255;
//                 state->col_lens[src]--;

//                 move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src, (uint8_t)f_slot, card, 1};

//                 if (solve(state, depth + 1)) return true;

//                 // Backtrack
//                 state->col_lens[src]++;
//                 state->columns[src][len - 1] = card;
//                 state->freecells[f_slot] = 255;
//             }
//             // FALL 2: Atomarer Meta-Move für Sequenzen (seq_len > 1)
//             // Nur ausführen, wenn wir genug FreeCells haben UND die Spalte nicht komplett aus der Sequenz besteht
//             else if (seq_len > 1 && seq_len <= free_cells_count && len > seq_len)
//             {
//                 // Wir legen ALLE seq_len Karten der Sequenz in EINEM Schritt ab,
//                 // um die Karte DARUNTER freizulegen!

//                 // Zug ausführen
//                 for (int i = 0; i < seq_len; i++) {
//                     uint8_t card = state->columns[src][len - 1 - i];
//                     int f_slot = free_indices[i];
//                     state->freecells[f_slot] = card;
//                     state->columns[src][len - 1 - i] = 255;
//                 }
//                 state->col_lens[src] -= seq_len;

//                 move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src, (uint8_t)free_indices[0],
//                                              state->columns[src][len - seq_len], (uint8_t)seq_len};

//                 if (solve(state, depth + 1)) return true;

//                 // Backtrack
//                 state->col_lens[src] += seq_len;
//                 for (int i = 0; i < seq_len; i++) {
//                     int f_slot = free_indices[i];
//                     uint8_t card = state->freecells[f_slot];
//                     state->columns[src][len - seq_len + i] = card;
//                     state->freecells[f_slot] = 255;
//                 }
//             }
//         }
//     }

//     return false; // Kein Weg gefunden
// }

// // Maximale Kartenanzahl, die als Block auf EINE Zielspalte bewegt werden kann
// static inline int max_movable_cards(int free_cells, int empty_cols, bool dst_is_empty)
// {
//     // Wenn die Zielspalte leer ist, steht sie nicht als freier Zwischenspeicher zur Verfügung
//     int E = empty_cols - (dst_is_empty ? 1 : 0);
//     if (E < 0)
//         E = 0;
//     return (free_cells + 1) * (1 << E);
// }

// Maximale Gesamtkapazität zum Evakuieren / Zerlegen einer Sequenz (FreeCells + leere Spalten)
static inline int max_evacuable_cards(int free_cells, int empty_cols)
{
    if (empty_cols == 0)
        return free_cells;
    return ((free_cells + 1) * (1 << empty_cols) - 1) + free_cells;
}

// bool solve(GameState *state, int depth)
// {
//     if (depth >= MAX_DEPTH)
//         return false;

//     // 1. Siegbedingung prüfen
//     if (is_solved(state))
//         return true;

//     // =========================================================================
//     // 1. SAFE MOVES / FOUNDATION MOVES (PRIORITÄT 1)
//     // =========================================================================

//     // A) Tableau -> Foundation
//     for (int src = 0; src < NUM_COLUMNS; src++)
//     {
//         int len = state->col_lens[src];
//         if (len == 0)
//             continue;

//         uint8_t card = state->columns[src][len - 1];
//         uint8_t suit = card / 13;
//         uint8_t rank = card % 13;

//         uint8_t f_card = state->foundations[suit];
//         int required_rank = (f_card == 255) ? 0 : (f_card % 13) + 1;

//         if (rank == required_rank)
//         {
//             state->foundations[suit] = card;
//             state->columns[src][len - 1] = 255;
//             state->col_lens[src]--;

//             move_history[depth] = (Move){MOVE_TABLEAU_TO_FOUNDATION, (uint8_t)src, suit, card, 1};

//             if (solve(state, depth + 1))
//                 return true;

//             // Backtrack
//             state->col_lens[src]++;
//             state->columns[src][len - 1] = card;
//             state->foundations[suit] = f_card;

//             // Safe Move Pruning: Direkt abbrechen, keine weiteren Züge im selben Zustand testen!
//             return false;
//         }
//     }

//     // B) FreeCell -> Foundation
//     for (int f = 0; f < NUM_FREECELLS; f++)
//     {
//         if (state->freecells[f] == 255)
//             continue;

//         uint8_t card = state->freecells[f];
//         uint8_t suit = card / 13;
//         uint8_t rank = card % 13;

//         uint8_t f_card = state->foundations[suit];
//         int required_rank = (f_card == 255) ? 0 : (f_card % 13) + 1;

//         if (rank == required_rank)
//         {
//             state->foundations[suit] = card;
//             state->freecells[f] = 255;

//             move_history[depth] = (Move){MOVE_FREECELL_TO_FOUNDATION, (uint8_t)f, suit, card, 1};

//             if (solve(state, depth + 1))
//                 return true;

//             // Backtrack
//             state->freecells[f] = card;
//             state->foundations[suit] = f_card;

//             return false;
//         }
//     }

//     // Vorab-Berechnung freier Ressourcen
//     int free_cells_count = 0;
//     int free_indices[NUM_FREECELLS];
//     for (int f = 0; f < NUM_FREECELLS; f++)
//     {
//         if (state->freecells[f] == 255)
//         {
//             free_indices[free_cells_count++] = f;
//         }
//     }

//     int empty_cols_count = 0;
//     for (int c = 0; c < NUM_COLUMNS; c++)
//     {
//         if (state->col_lens[c] == 0)
//             empty_cols_count++;
//     }

//     // =========================================================================
//     // 2. BACKTRACKING: TABLEAU -> TABLEAU (META-MOVES)
//     // =========================================================================
//     for (int src = 0; src < NUM_COLUMNS; src++)
//     {
//         if (state->col_lens[src] == 0)
//             continue;

//         int seq_len = get_sequence_length(state, src);

//         for (int dst = 0; dst < NUM_COLUMNS; dst++)
//         {
//             if (src == dst)
//                 continue;

//             bool dst_is_empty = (state->col_lens[dst] == 0);
//             int max_cards = max_movable_cards(free_cells_count, empty_cols_count, dst_is_empty);

//             if (dst_is_empty)
//             {
//                 // ZIELSPALTE IST LEER:
//                 // Nur k = seq_len erlauben. Niemals eine Sequenz zerreißen, um nur Teile auf leere Spalten zu legen!
//                 // Und nur verschieben, wenn die Sequenz NICHT die ganze Spalte bildet (Isomorphie).
//                 if (seq_len < state->col_lens[src] && seq_len <= max_cards)
//                 {
//                     int k = seq_len;
//                     uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

//                     int src_start = state->col_lens[src] - k;
//                     for (int i = 0; i < k; i++)
//                     {
//                         state->columns[dst][i] = state->columns[src][src_start + i];
//                         state->columns[src][src_start + i] = 255;
//                     }
//                     state->col_lens[src] -= k;
//                     state->col_lens[dst] = k;

//                     move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k};

//                     if (solve(state, depth + 1))
//                         return true;

//                     // Backtrack
//                     state->col_lens[src] += k;
//                     state->col_lens[dst] = 0;
//                     for (int i = 0; i < k; i++)
//                     {
//                         state->columns[src][src_start + i] = state->columns[dst][i];
//                         state->columns[dst][i] = 255;
//                     }
//                 }
//             }
//             else
//             {
//                 // ZIELSPALTE IST NICHT LEER:
//                 uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
//                 int movable_limit = (seq_len < max_cards) ? seq_len : max_cards;

//                 for (int k = 1; k <= movable_limit; k++)
//                 {
//                     uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

//                     // Bäckers Spiel: Gleiche Farbe, Rang - 1
//                     if ((top_card_of_group + 4) == dst_card)
//                     {
//                         int src_start = state->col_lens[src] - k;
//                         for (int i = 0; i < k; i++)
//                         {
//                             state->columns[dst][state->col_lens[dst] + i] = state->columns[src][src_start + i];
//                             state->columns[src][src_start + i] = 255;
//                         }
//                         state->col_lens[src] -= k;
//                         state->col_lens[dst] += k;

//                         move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k};

//                         if (solve(state, depth + 1))
//                             return true;

//                         // Backtrack
//                         state->col_lens[src] += k;
//                         state->col_lens[dst] -= k;
//                         for (int i = 0; i < k; i++)
//                         {
//                             state->columns[src][src_start + i] = state->columns[dst][state->col_lens[dst] + i];
//                             state->columns[dst][state->col_lens[dst] + i] = 255;
//                         }

//                         // Jede Karte ist eindeutig – nur genau ein k kann passen
//                         break;
//                     }
//                 }
//             }
//         }
//     }

//     // =========================================================================
//     // 3. BACKTRACKING: FREECELL -> TABLEAU
//     // =========================================================================
//     for (int f = 0; f < NUM_FREECELLS; f++)
//     {
//         if (state->freecells[f] == 255)
//             continue;

//         uint8_t card = state->freecells[f];

//         for (int dst = 0; dst < NUM_COLUMNS; dst++)
//         {
//             bool dst_is_empty = (state->col_lens[dst] == 0);

//             bool valid = false;
//             if (dst_is_empty)
//             {
//                 valid = true;
//             }
//             else
//             {
//                 uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
//                 if ((card + 4) == dst_card)
//                 {
//                     valid = true;
//                 }
//             }

//             if (valid)
//             {
//                 state->columns[dst][state->col_lens[dst]] = card;
//                 state->col_lens[dst]++;
//                 state->freecells[f] = 255;

//                 move_history[depth] = (Move){MOVE_FREECELL_TO_TABLEAU, (uint8_t)f, (uint8_t)dst, card, 1};

//                 if (solve(state, depth + 1))
//                     return true;

//                 // Backtrack
//                 state->freecells[f] = card;
//                 state->col_lens[dst]--;
//                 state->columns[dst][state->col_lens[dst]] = 255;
//             }
//         }
//     }

//     // =========================================================================
//     // 4. BACKTRACKING: TABLEAU -> FREECELLS (PRUNING & ATOMARE MOVES)
//     // =========================================================================
//     if (free_cells_count > 0)
//     {
//         for (int src = 0; src < NUM_COLUMNS; src++)
//         {
//             int len = state->col_lens[src];
//             if (len == 0)
//                 continue;

//             int seq_len = get_sequence_length(state, src);

//             // FALL 1: Einzelne Karte am Ende (keine Sequenz mit der Karte darüber)
//             if (seq_len == 1)
//             {
//                 int f_slot = free_indices[0]; // Ersten freien Slot nutzen (Isomorphie)
//                 uint8_t card = state->columns[src][len - 1];

//                 state->freecells[f_slot] = card;
//                 state->columns[src][len - 1] = 255;
//                 state->col_lens[src]--;

//                 move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src, (uint8_t)f_slot, card, 1};

//                 if (solve(state, depth + 1))
//                     return true;

//                 // Backtrack
//                 state->col_lens[src]++;
//                 state->columns[src][len - 1] = card;
//                 state->freecells[f_slot] = 255;
//             }
//             // FALL 2: Atomarer Meta-Move für Sequenzen (seq_len > 1)
//             else if (seq_len > 1 && len > seq_len)
//             {
//                 int max_evac = max_evacuable_cards(free_cells_count, empty_cols_count);

//                 // Pruning: Haben wir insgesamt genug Kapazität, um an das verdeckte Material zu kommen?
//                 // Für diesen atomaren Schritt müssen zusätzlich ausreichend freie FreeCells bereitstehen.
//                 if (seq_len <= max_evac && seq_len <= free_cells_count)
//                 {
//                     for (int i = 0; i < seq_len; i++)
//                     {
//                         uint8_t card = state->columns[src][len - 1 - i];
//                         int f_slot = free_indices[i];
//                         state->freecells[f_slot] = card;
//                         state->columns[src][len - 1 - i] = 255;
//                     }
//                     state->col_lens[src] -= seq_len;

//                     move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src, (uint8_t)free_indices[0],
//                                                  state->columns[src][len - seq_len], (uint8_t)seq_len};

//                     if (solve(state, depth + 1))
//                         return true;

//                     // Backtrack
//                     state->col_lens[src] += seq_len;
//                     for (int i = 0; i < seq_len; i++)
//                     {
//                         int f_slot = free_indices[i];
//                         uint8_t card = state->freecells[f_slot];
//                         state->columns[src][len - seq_len + i] = card;
//                         state->freecells[f_slot] = 255;
//                     }
//                 }
//             }
//         }
//     }

//     return false;
// }

// buggy:
// bool solve(GameState *state, int depth)
// {
//     if (depth >= MAX_DEPTH)
//         return false;

//     // 1. Siegbedingung prüfen
//     if (is_solved(state))
//         return true;

//     // =========================================================================
//     // 1. SAFE MOVES / FOUNDATION MOVES (PRIORITÄT 1)
//     // =========================================================================

//     // A) Tableau -> Foundation
//     for (int src = 0; src < NUM_COLUMNS; src++)
//     {
//         int len = state->col_lens[src];
//         if (len == 0) continue;

//         uint8_t card = state->columns[src][len - 1];
//         uint8_t suit = card % 4; // FARBE = Rest bei Division durch 4
//         uint8_t rank = card / 4; // RANG = Quotient bei Division durch 4

//         // Passt die Karte genau als nächste auf die Foundation dieser Farbe?
//         if (rank == state->foundations[suit])
//         {
//             state->foundations[suit]++;
//             state->columns[src][len - 1] = 255;
//             state->col_lens[src]--;

//             move_history[depth] = (Move){MOVE_TABLEAU_TO_FOUNDATION, (uint8_t)src, suit, card, 1};

//             if (solve(state, depth + 1)) return true;

//             // Backtrack
//             state->col_lens[src]++;
//             state->columns[src][len - 1] = card;
//             state->foundations[suit]--;

//             // Safe Move Pruning
//             return false;
//         }
//     }

//     // B) FreeCell -> Foundation
//     for (int f = 0; f < NUM_FREECELLS; f++)
//     {
//         if (state->freecells[f] == 255) continue;

//         uint8_t card = state->freecells[f];
//         uint8_t suit = card % 4; // FARBE = Rest bei Division durch 4
//         uint8_t rank = card / 4; // RANG = Quotient bei Division durch 4

//         if (rank == state->foundations[suit])
//         {
//             state->foundations[suit]++;
//             state->freecells[f] = 255;

//             move_history[depth] = (Move){MOVE_FREECELL_TO_FOUNDATION, (uint8_t)f, suit, card, 1};

//             if (solve(state, depth + 1)) return true;

//             // Backtrack
//             state->freecells[f] = card;
//             state->foundations[suit]--;

//             return false;
//         }
//     }

//     // Vorab-Berechnung freier Ressourcen
//     int free_cells_count = 0;
//     int free_indices[NUM_FREECELLS];
//     for (int f = 0; f < NUM_FREECELLS; f++) {
//         if (state->freecells[f] == 255) {
//             free_indices[free_cells_count++] = f;
//         }
//     }

//     int empty_cols_count = 0;
//     for (int c = 0; c < NUM_COLUMNS; c++) {
//         if (state->col_lens[c] == 0) empty_cols_count++;
//     }

//     // =========================================================================
//     // 2. BACKTRACKING: TABLEAU -> TABLEAU (META-MOVES)
//     // =========================================================================
//     for (int src = 0; src < NUM_COLUMNS; src++)
//     {
//         if (state->col_lens[src] == 0) continue;

//         int seq_len = get_sequence_length(state, src);

//         for (int dst = 0; dst < NUM_COLUMNS; dst++)
//         {
//             if (src == dst) continue;

//             bool dst_is_empty = (state->col_lens[dst] == 0);
//             int max_cards = max_movable_cards(free_cells_count, empty_cols_count, dst_is_empty);

//             if (dst_is_empty)
//             {
//                 // ZIELSPALTE IST LEER:
//                 // Nur ganze Sequenzen verschieben (seq_len) und Isomorphie beachten
//                 if (seq_len < state->col_lens[src] && seq_len <= max_cards)
//                 {
//                     int k = seq_len;
//                     uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

//                     int src_start = state->col_lens[src] - k;
//                     for (int i = 0; i < k; i++) {
//                         state->columns[dst][i] = state->columns[src][src_start + i];
//                         state->columns[src][src_start + i] = 255;
//                     }
//                     state->col_lens[src] -= k;
//                     state->col_lens[dst] = k;

//                     move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k};

//                     if (solve(state, depth + 1)) return true;

//                     // Backtrack
//                     state->col_lens[src] += k;
//                     state->col_lens[dst] = 0;
//                     for (int i = 0; i < k; i++) {
//                         state->columns[src][src_start + i] = state->columns[dst][i];
//                         state->columns[dst][i] = 255;
//                     }
//                 }
//             }
//             else
//             {
//                 // ZIELSPALTE IST NICHT LEER:
//                 uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
//                 int movable_limit = (seq_len < max_cards) ? seq_len : max_cards;

//                 for (int k = 1; k <= movable_limit; k++)
//                 {
//                     uint8_t top_card_of_group = state->columns[src][state->col_lens[src] - k];

//                     // Bäckers Spiel Regel: Gleiche Farbe, Rang - 1
//                     if ((top_card_of_group + 4) == dst_card)
//                     {
//                         int src_start = state->col_lens[src] - k;
//                         for (int i = 0; i < k; i++) {
//                             state->columns[dst][state->col_lens[dst] + i] = state->columns[src][src_start + i];
//                             state->columns[src][src_start + i] = 255;
//                         }
//                         state->col_lens[src] -= k;
//                         state->col_lens[dst] += k;

//                         move_history[depth] = (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst, top_card_of_group, (uint8_t)k};

//                         if (solve(state, depth + 1)) return true;

//                         // Backtrack
//                         state->col_lens[src] += k;
//                         state->col_lens[dst] -= k;
//                         for (int i = 0; i < k; i++) {
//                             state->columns[src][src_start + i] = state->columns[dst][state->col_lens[dst] + i];
//                             state->columns[dst][state->col_lens[dst] + i] = 255;
//                         }

//                         break;
//                     }
//                 }
//             }
//         }
//     }

//     // =========================================================================
//     // 3. BACKTRACKING: FREECELL -> TABLEAU
//     // =========================================================================
//     for (int f = 0; f < NUM_FREECELLS; f++)
//     {
//         if (state->freecells[f] == 255) continue;

//         uint8_t card = state->freecells[f];

//         for (int dst = 0; dst < NUM_COLUMNS; dst++)
//         {
//             bool dst_is_empty = (state->col_lens[dst] == 0);

//             bool valid = false;
//             if (dst_is_empty)
//             {
//                 valid = true;
//             }
//             else
//             {
//                 uint8_t dst_card = state->columns[dst][state->col_lens[dst] - 1];
//                 if ((card + 4) == dst_card) {
//                     valid = true;
//                 }
//             }

//             if (valid)
//             {
//                 state->columns[dst][state->col_lens[dst]] = card;
//                 state->col_lens[dst]++;
//                 state->freecells[f] = 255;

//                 move_history[depth] = (Move){MOVE_FREECELL_TO_TABLEAU, (uint8_t)f, (uint8_t)dst, card, 1};

//                 if (solve(state, depth + 1)) return true;

//                 // Backtrack
//                 state->freecells[f] = card;
//                 state->col_lens[dst]--;
//                 state->columns[dst][state->col_lens[dst]] = 255;
//             }
//         }
//     }

//     // =========================================================================
//     // 4. BACKTRACKING: TABLEAU -> FREECELLS (PRUNING & ATOMARE MOVES)
//     // =========================================================================
//     if (free_cells_count > 0)
//     {
//         for (int src = 0; src < NUM_COLUMNS; src++)
//         {
//             int len = state->col_lens[src];
//             if (len == 0) continue;

//             int seq_len = get_sequence_length(state, src);

//             // FALL 1: Einzelne Karte am Ende
//             if (seq_len == 1)
//             {
//                 int f_slot = free_indices[0];
//                 uint8_t card = state->columns[src][len - 1];

//                 state->freecells[f_slot] = card;
//                 state->columns[src][len - 1] = 255;
//                 state->col_lens[src]--;

//                 move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src, (uint8_t)f_slot, card, 1};

//                 if (solve(state, depth + 1)) return true;

//                 // Backtrack
//                 state->col_lens[src]++;
//                 state->columns[src][len - 1] = card;
//                 state->freecells[f_slot] = 255;
//             }
//             // FALL 2: Atomarer Meta-Move für Sequenzen
//             else if (seq_len > 1 && len > seq_len)
//             {
//                 int max_evac = max_evacuable_cards(free_cells_count, empty_cols_count);

//                 if (seq_len <= max_evac && seq_len <= free_cells_count)
//                 {
//                     for (int i = 0; i < seq_len; i++) {
//                         uint8_t card = state->columns[src][len - 1 - i];
//                         int f_slot = free_indices[i];
//                         state->freecells[f_slot] = card;
//                         state->columns[src][len - 1 - i] = 255;
//                     }
//                     state->col_lens[src] -= seq_len;

//                     move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src, (uint8_t)free_indices[0],
//                                                  state->columns[src][len - seq_len], (uint8_t)seq_len};

//                     if (solve(state, depth + 1)) return true;

//                     // Backtrack
//                     state->col_lens[src] += seq_len;
//                     for (int i = 0; i < seq_len; i++) {
//                         int f_slot = free_indices[i];
//                         uint8_t card = state->freecells[f_slot];
//                         state->columns[src][len - seq_len + i] = card;
//                         state->freecells[f_slot] = 255;
//                     }
//                 }
//             }
//         }
//     }

//     return false;
// }

// --- DRUCK-FUNKTIONEN ---
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
    printf(" LÖSUNG GEFUNDEN IN %d ZÜGEN:\n", total_solution_moves);
    printf("====================================\n\n");

    for (int i = 0; i < total_solution_moves; i++)
    {
        Move m = move_history[i];
        printf("Zug %3d: ", i + 1);

        switch (m.type)
        {
        case MOVE_TABLEAU_TO_FOUNDATION:
            printf("Spalte %d   -> Zielstapel  [", m.src + 1);
            print_card(m.card);
            printf("]\n");
            break;
        case MOVE_FREECELL_TO_FOUNDATION:
            printf("FreeCell %d -> Zielstapel  [", m.src + 1);
            print_card(m.card);
            printf("]\n");
            break;
        case MOVE_TABLEAU_TO_TABLEAU:
            printf("Spalte %d   -> Spalte %d     [", m.src + 1, m.dst + 1);
            print_card(m.card);
            printf("]\n");
            break;
        case MOVE_TABLEAU_TO_FREECELL:
            printf("Spalte %d   -> FreeCell %d   [", m.src + 1, m.dst + 1);
            print_card(m.card);
            printf("]\n");
            break;
        case MOVE_FREECELL_TO_TABLEAU:
            printf("FreeCell %d -> Spalte %d     [", m.src + 1, m.dst + 1);
            print_card(m.card);
            printf("]\n");
            break;
        }

        print_game_state(&m.gameState);
        skipInputLine();
    }
    printf("\n");
}

// Liest Karten im Format "p k", "pk", "kr 10", "h,2", "k;a" etc.
int parse_card(const char *suit_str, const char *rank_str, uint8_t *out_card)
{
    // 1. Farbe ermitteln
    uint8_t suit = 255;
    if (strcmp(suit_str, "p") == 0)
        suit = 0; // Pik
    else if (strcmp(suit_str, "h") == 0)
        suit = 1; // Herz
    else if (strcmp(suit_str, "k") == 0)
        suit = 2; // Karo
    else if (strcmp(suit_str, "kr") == 0)
        suit = 3; // Kreuz
    else
        return -1;

    // 2. Rang ermitteln
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

    // 1. Karten im Tableau zählen und markieren
    for (int col = 0; col < NUM_COLUMNS; col++)
    {
        for (int i = 0; i < game->col_lens[col]; i++)
        {
            uint8_t card = game->columns[col][i];

            if (card >= 52)
            {
                printf("\nFehler: Ungültiger Kartenwert (%d) gefunden!\n", card);
                return false;
            }

            if (seen[card])
            {
                printf("\nFehler: Karte ");
                print_card(card);
                printf(" ist DOPPELT im Spielfeld vorhanden!\n");
                return false;
            }

            seen[card] = true;
            card_count++;
        }
    }

    // 2. Prüfen, ob eine Karte fehlt
    if (card_count != 52)
    {
        printf("\nFehler: Es wurden nur %d statt 52 Karten eingelesen!\n", card_count);
        printf("Folgende Karten FEHLEN:\n");

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

    printf("\n--> Validierung erfolgreich: Genau 52 eindeutige Karten eingelesen!\n");
    return true;
}

bool parse_board_from_stdin(GameState *out_game)
{
    memset(out_game, 0, sizeof(GameState));
    memset(out_game->freecells, 255, 4);

    char line_buf[512];
    int current_col = 0;

    printf("--- Bitte Spielfeld eingeben (8 Spalten) ---\n");

    while (current_col < 8 && fgets(line_buf, sizeof(line_buf), stdin))
    {
        char *l = line_buf;
        while (isspace(*l))
            l++;

        if (*l == '\0' || *l == '#')
            continue;

        if (strncmp(l, "-", 1) == 0)
        {
            out_game->col_lens[current_col++] = 0;
            printf("Spalte %d eingelesen (0 Karten - Leer)\n", current_col);
            continue;
        }

        char *ptr = l;
        while (*ptr && out_game->col_lens[current_col] < 19)
        {
            // Whitespace, Kommas, Strichpunkte überspringen
            while (*ptr && (isspace(*ptr) || *ptr == ',' || *ptr == ';'))
                ptr++;
            if (*ptr == '\0')
                break;

            // Farbe lesen
            char suit_buf[8] = {0};
            int s_idx = 0;
            while (*ptr && isalpha(*ptr) && s_idx < 7)
            {
                suit_buf[s_idx++] = (char)tolower(*ptr++);
            }

            // Whitespace zwischen Farbe und Rang überspringen
            while (*ptr && isspace(*ptr))
                ptr++;

            // Rang lesen
            char rank_buf[8] = {0};
            int r_idx = 0;
            while (*ptr && isalnum(*ptr) && r_idx < 7)
            {
                rank_buf[r_idx++] = (char)tolower(*ptr++);
            }

            if (s_idx == 0 || r_idx == 0)
            {
                printf("\nFehler: Unvollständige Karte in Spalte %d nahe '%s'\n", current_col + 1, ptr);
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
                printf("\nFehler: Ungültige Karte '%s %s' in Spalte %d!\n", suit_buf, rank_buf, current_col + 1);
                return false;
            }
        }

        printf("Spalte %d eingelesen (%d Karten)\n", current_col + 1, out_game->col_lens[current_col]);
        current_col++;
    }

    if (current_col < 8)
    {
        printf("\nFehler: Nur %d von 8 Spalten eingelesen!\n", current_col);
        return false;
    }

    // Unbedingt das Deck auf Vollständigkeit (exakt 52 eindeutige Karten) prüfen!
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
    printf("\n=================================== AKTUELLER ZUSTAND ===================================\n");

    // 1. Foundations & FreeCells
    printf("FreeCells:   ");
    for (int f = 0; f < 4; f++)
    {
        printf("[");
        print_card(s->freecells[f]);
        printf("] ");
    }
    printf("      Foundations: ");
    // const char *suits[] = {"Pik", "Herz", "Karo", "Kreuz"};
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

    // 2. Maximum Höhe im Tableau ermitteln
    int max_len = 0;
    for (int col = 0; col < 8; col++)
    {
        if (s->col_lens[col] > max_len)
            max_len = s->col_lens[col];
    }

    // Header für die Spalten (exakt 12 Zeichen breit je Spalte)
    for (int col = 0; col < 8; col++)
    {
        char header[16];
        snprintf(header, sizeof(header), "Spalte %d", col + 1);
        printf("%-10s", header);
    }
    printf("\n");

    // Tableau Zeile für Zeile von oben nach unten ausgeben
    for (int row = 0; row < max_len; row++)
    {
        for (int col = 0; col < 8; col++)
        {
            if (row < s->col_lens[col])
            {
                uint8_t card = s->columns[col][row];

                // Karte erst in einen String formatieren
                char card_str[32];
                // Hilfspuffer für print_card-Äquivalent:
                // const char *suit_names[] = {"Pik", "Herz", "Karo", "Kreuz"};
                const char *rank_names[] = {"--", "A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "B", "D", "K"};

                uint8_t suit = card & 3;
                uint8_t rank = (card >> 2) + 1;

                print_card(card);
                printf("      ");
                // if (card == 255)
                // {
                //     snprintf(card_str, sizeof(card_str), "---");
                // }
                // else
                // {
                //     snprintf(card_str, sizeof(card_str), "%s %s", suits[suit], rank_names[rank]);
                // }

                // // Exakt auf 12 Zeichen Breite linksbündig auffüllen
                // printf("%-12s", card_str);
            }
            else
            {
                printf("%-10s", ""); // Leeres Feld
            }
        }
        printf("\n");
    }
    printf("=========================================================================================\n\n");
}

int main(void)
{
    arena_buffer = calloc(ARENA_SIZE, 1);
    hash_buckets = calloc(HASH_TABLE_SIZE, sizeof(uint32_t));

    if (!arena_buffer || !hash_buckets)
    {
        fprintf(stderr, "Speicher konnte nicht allokiert werden.\n");
        return 1;
    }

    GameState game;

    if (!parse_board_from_stdin(&game))
    {
        fprintf(stderr, "\nFehler beim Einlesen von stdin! Abbruch.\n");
        free(arena_buffer);
        free(hash_buckets);
        return 1;
    }

    printf("\nSuche Lösung für das eingelesene Spielfeld...\n");
    print_game_state(&game);

    if (solve(&game, 0))
    {
        print_solution();
        printf("Eindeutige Zustände im RAM: %zu Bytes in der Arena verbraucht.\n", arena_offset);
    }
    else
    {
        printf("Keine Lösung gefunden.\n");
    }

    printf("Eindeutige Zustände im RAM: %zu Bytes in der Arena verbraucht.\n", arena_offset);
    printf("steps %lld\n", steps);

    free(arena_buffer);
    free(hash_buckets);
    return 0;
}

// void myPrint(char **pbuf, size_t *psize, const char *format, ...)
// {
//     va_list ap;
//     va_start(ap, format);
//     int len = vsnprintf(*pbuf, *psize, format, ap);
//     va_end(ap);
//     int d = min(len, *psize);
//     *pbuf += d;
//     *psize -= d;
// }

// void snprint_card(char **pbuf, size_t *psize, uint8_t card)
// {

//     if (card == 255)
//     {
//         myPrint(pbuf, psize, "----");
//         return;
//     }
//     uint8_t suit = card & 3;
//     uint8_t rank = card >> 2;
//     if (suit == 1 || suit == 2)
//     {
//         myPrint(pbuf, psize, "%s", ANSI_ROT);
//     }
//     myPrint(pbuf, psize, "%s %s", suits[suit], ranks[rank]);
//     if (suit == 1 || suit == 2)
//     {
//         myPrint(pbuf, psize, "%s", ANSI_RESET);
//     }
// }
