#define _GNU_SOURCE

#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>

#define ARENA_SIZE (8ULL * 1024 * 1024 * 1024) // 8 GB for the arena
// ~67 million buckets (needs only about 268 MB of RAM for hash_buckets)
#define HASH_TABLE_SIZE (67108859 * 2 - 1) // (maybe) prime number
// #define HASH_TABLE_SIZE 8388607             // prime number for open
// addressing
#define MAX_DEPTH 254
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

static inline int min(int a, int b) {
  if (a < b)
    return a;
  return b;
}

// --- TYPES & STRUCTURES ---

#define SPADES 0
#define HEARTS 1
#define DIAMONDS 2
#define CLUBS 3

// Suits: 0 = spades, 1 = hearts, 2 = diamonds, 3 = clubs
// Rank:  0 (ace) through 12 (king)
// Formula: card = (rank * 4) + suit (0..51, 255 = empty)

typedef struct {
  uint8_t columns[NUM_COLUMNS][19];
  uint8_t col_lens[NUM_COLUMNS];
  uint8_t freecells[NUM_FREECELLS]; // 255 = empty
  uint8_t
      foundations[4]; // Highest solved rank (0 = none, 1 = ace, ..., 13 = king)
} GameState;

typedef enum {
  MOVE_TABLEAU_TO_FOUNDATION,
  MOVE_FREECELL_TO_FOUNDATION,
  MOVE_TABLEAU_TO_TABLEAU,
  MOVE_TABLEAU_TO_FREECELL,
  MOVE_FREECELL_TO_TABLEAU
} MoveType;

typedef struct {
  MoveType type;
  uint8_t src;
  uint8_t dst;
  uint8_t card;
  uint8_t count; // NEW: number of cards moved (for meta-moves)
  GameState gameState;
} Move;

// --- GLOBAL MEMORY SYSTEMS ---

static uint8_t *arena_buffer = NULL;
// static uint8_t arena_buffer[ARENA_SIZE];
static int64_t arena_offset = 0;
static uint64_t *hash_buckets = NULL;
// static uint32_t hash_buckets[HASH_TABLE_SIZE];

static Move move_history[MAX_DEPTH];
// static Move move_history[100];
static uint64_t maxProbes = 0;
static uint64_t steps = 0;
static uint64_t cycles = 0;
static uint64_t shortages = 0;
static uint64_t hash_entries = 0;
static uint64_t depthAborts = 0;
static int bestSolutionDepth = MAX_DEPTH + 1;
static int64_t bestSolutionArenaIndex = -1;
static Move bestMoveHistory[MAX_DEPTH];

static bool searchForBest = true;

static const char *suits[] = {"♠", "♥", "♦", "♣"};
static const char *ranks[] = {" A", " 2", " 3", " 4", " 5", " 6", " 7",
                              " 8", " 9", "10", " J", " Q", " K"};

// forward declarations
void print_move(const Move *pm);
void print_card(uint8_t card);
void print_game_state(const GameState *s);
void pause();
void print_moves(const Move *move_history, int numMoves, bool interactive,
                 const char *header);

// --- ARITHMETIC & HELPERS ---

uint8_t make_card(uint8_t rank_1_to_13, uint8_t suit_0_to_3) {
  return ((rank_1_to_13 - 1) << 2) | (suit_0_to_3 & 3);
}

uint8_t card_suit(uint8_t card) { return card & 3; }
uint8_t card_rank(uint8_t card) { return (card >> 2) + 1; }

// static bool cmp_verbose = false;
// static bool depthAbortsVerbose = false;

// --- CANONICAL PACKING & HASH SET ---

int compColumn(const void *a1, const void *b1, void *s1) {
  const int *a = (const int *)a1;
  const int *b = (const int *)b1;
  // if (cmp_verbose)
  //     printf("compColumn: *a=%d, *b=%d\n", *a, *b);
  const GameState *s = (const GameState *)s1;
  // 1. Empty columns first
  // 2. Then compare the first card

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
      // if (cmp_verbose)
      // {
      //     printf("comp cards ");
      //     print_card(s->columns[*a][0]);
      //     printf("   ");
      //     print_card(s->columns[*b][0]);
      //     printf("\n");
      // }
      return (int)s->columns[*a][0] - (int)s->columns[*b][0];
    }
  }
}

int pack_state(const GameState *s, uint8_t *buf) {
  int idx = 0;

  // 1. Foundations (4 Bytes)
  for (int i = 0; i < 4; i++)
    buf[idx++] = s->foundations[i];

  // 2. Sort FreeCells (symmetry breaking) and pack them (NUM_FREECELLS bytes)
  uint8_t fc[NUM_FREECELLS];
  memcpy(fc, s->freecells, NUM_FREECELLS);
  for (int i = 0; i < NUM_FREECELLS - 1; i++) {
    for (int j = i + 1; j < NUM_FREECELLS; j++) {
      if (fc[i] > fc[j]) {
        uint8_t tmp = fc[i];
        fc[i] = fc[j];
        fc[j] = tmp;
      }
    }
  }
  // if (cmp_verbose)
  // {
  //     printf("Sorted free cells:");
  //     for (int i = 0; i < NUM_FREECELLS; ++i)
  //     {
  //         printf("[");
  //         print_card(fc[i]);
  //         printf("]");
  //     }
  //     printf("\n");
  // }
  for (int i = 0; i < NUM_FREECELLS; i++)
    buf[idx++] = fc[i];

  // 3. Sort tableau columns
  int sorted[NUM_COLUMNS];
  for (int i = 0; i < NUM_COLUMNS; ++i) {
    sorted[i] = i;
  }
  qsort_r(sorted, NUM_COLUMNS, sizeof(int), &compColumn, (void *)s);

  // if (cmp_verbose)
  // {
  //     print_game_state(s);
  //     printf("Sorted columns (1-based): ");
  //     for (int i = 0; i < NUM_COLUMNS; ++i)
  //     {
  //         printf("%d ", sorted[i] + 1);
  //     }
  // }

  // 3. Tableau columns
  for (int colI = 0; colI < NUM_COLUMNS; colI++) {
    int col = sorted[colI];
    buf[idx++] = s->col_lens[col];
    for (int i = 0; i < s->col_lens[col]; i++) {
      buf[idx++] = s->columns[col][i];
    }
  }

  return idx; // Exact total length
}

uint32_t hash_bytes(const uint8_t *data, size_t len) {
  uint32_t hash = 2166136261u;
  for (size_t i = 0; i < len; i++) {
    hash ^= data[i];
    hash *= 16777619u;
  }
  return hash;
}

void dumpCounts() {
  printf("[maxProbes %" PRIu64 "6] [steps %14" PRIu64 "] [cycles %14" PRIu64
         "] [shortages %14" PRIu64 "] [hash_entries %14" PRIu64
         "] [arena_offset %14" PRIu64 "]\n",
         maxProbes, steps, cycles, shortages, hash_entries, arena_offset);
}

GameState bugState, bugState2;
uint8_t packedBugState[200];
int packedBugStateLen;
bool visitedBugState = false;

bool is_visited_or_add(const GameState *state, int *arenaIndex, uint8_t depth) {
  ++steps;

  // if (steps % 2000000 == 0)
  // // if (steps > 12000)
  // // if (true)
  // {
  //     printf("\n>>> SNAPSHOT after %" PRIu64 " states (arena: %.2f MB -
  //     %.2f%%) <<<\n",
  //            steps,
  //            (double)arena_offset / (1024.0 * 1024.0),
  //         arena_offset * 100.0 / ARENA_SIZE);
  //     print_game_state(state);
  //     printf("Shortest known solution: %d moves\n", bestSolutionDepth);
  // }

  uint8_t tmp_buf[200];
  int len = pack_state(state, tmp_buf);
  assert(len <= 200);

//   if (len == packedBugStateLen && memcmp(packedBugState, tmp_buf, len) == 0) {
//     printf("Found packed bug state:\n");
//     print_game_state((state));
//     // visitedBugState = true;
//   }

  uint32_t hash = hash_bytes(tmp_buf, len);
  uint32_t index = hash % HASH_TABLE_SIZE;
  uint32_t probes = 0;

  // Search for a free slot OR the chosen state
  while (hash_buckets[index] != 0) {
    uint64_t existing_offset = hash_buckets[index] - 1;
    uint8_t *existing_data = &arena_buffer[existing_offset];
    uint8_t existingDepth;
    memcpy(&existingDepth, existing_data, sizeof(existingDepth));
    existing_data += sizeof(existingDepth);

    if (memcmp(existing_data, tmp_buf, len) == 0) {
      if (existingDepth <= depth) {
        // printf("existingDepth <= depth\n");
        // printf("existingDepth %d, depth %d\n", (int)existingDepth,
        // (int)depth);
        // // This way cannot be shorter than the one that has been calculated
        // earlier, so abort printf("Cycle!\n");
        // // if (cmp_verbose)
        // //     pause();

        ++cycles;
        return true; // Already visited!
      } else {
        // {
        //     if (bestSolutionDepth <= MAX_DEPTH)
        //     {
        //         printf("Old best moves (bestSolutionDepth %d)\n",
        //         bestSolutionDepth); for (int i = 0; i < bestSolutionDepth;
        //         ++i)
        //         {
        //             print_move(bestMoveHistory + i);
        //         }
        //     } else {
        //         printf("No solution, yet.\n");
        //     }

        //     printf("\nCurrent moves\n");
        //     for (int i = 0; i < depth; ++i)
        //     {
        //         print_move(move_history + i);
        //     }
        //     printf("\n");
        //     print_game_state(state);
        // }
        // printf("Shorter way found: \n");
        // printf("existingDepth %d, depth %d\n, bestSolutionDepth %d\n", (int)
        // existingDepth, (int) depth, bestSolutionDepth); pause();

        // Shorter way, so try again, after setting the new depth
        memcpy(existing_data - sizeof(existingDepth), &depth, sizeof(depth));
        ++shortages;
        return false;
      }
    }

    index = (index + 1) % HASH_TABLE_SIZE;
    probes++;

    // THE PROBES GUARD (prevents getting stuck!):
    if (probes >= HASH_TABLE_SIZE) {
      fprintf(stderr,
              "\n[ERROR] Hash table is full (%d buckets)! Please increase "
              "HASH_TABLE_SIZE.\n",
              HASH_TABLE_SIZE);
      exit(1);
    }
  }

  if (probes > maxProbes) {
    maxProbes = probes;
    dumpCounts();
  }

  // New -> write into the arena
  if (arena_offset + len > ARENA_SIZE) {
    fprintf(stderr, "\n[ERROR] Arena memory is full!\n");
    exit(1);
  }

  int64_t new_offset = arena_offset;
  *arenaIndex = new_offset;
  memcpy(&arena_buffer[new_offset], &depth, sizeof(depth));
  memcpy(&arena_buffer[new_offset] + sizeof(depth), tmp_buf, len);
  hash_buckets[index] = new_offset + 1; // 1-based offset
  arena_offset += sizeof(depth) + len;

  ++hash_entries;
  return false; // State was new
}
// --- CORE RECURSION & LOGIC ---

bool is_solved(const GameState *state) {
  return state->foundations[0] == 13 && state->foundations[1] == 13 &&
         state->foundations[2] == 13 && state->foundations[3] == 13;
}

// Calculates how many cards may be moved at once
int max_movable_cards1(int free_cells, int empty_cols, bool dst_is_empty) {
  if (dst_is_empty) {
    if (empty_cols == 0)
      return 0;
    // If the destination is empty, that column is not available as temporary
    // storage
    if (empty_cols == 0)
      return free_cells + 1;
    return (free_cells + 1) * (1 << (empty_cols - 1));
  } else {
    return (free_cells + 1) * (1 << empty_cols);
  }
}

// Returns the length of the valid sequence at the end of col (at least 1)
int get_sequence_length(const GameState *s, int col) {
  int len = s->col_lens[col];
  if (len <= 1)
    return len;

  const uint8_t *bottomCard = s->columns[col];
  const uint8_t *card = bottomCard + (len - 1);
  uint8_t suit = card_suit(*card);
  uint8_t lastRank = card_rank(*card);
  int seq_len = 1;

  while (card > bottomCard) {
    --card;
    uint8_t card_below = *card;

    uint8_t suit_below = card_suit(card_below);
    uint8_t rank_below = card_rank(card_below);

    // Baker's Game: same suit and rank exactly one lower
    if (suit_below == suit && rank_below == lastRank + 1) {
      lastRank = rank_below;
      seq_len++;
    } else {
      break; // Sequence broken
    }
  }
  return seq_len;
}

bool seqInFreecells(GameState *state, int freecell) {
  // Is the next-higher card of the same suit as the card in `freecell` in
  // another FreeCell or the top reachable card of a column? If so, the higher
  // card should be played instead, and this one must not be played.
  int card = state->freecells[freecell];
  if (card < 52) {
    int nextCard = card + 4;
    if (nextCard < 52) {
      for (int f = 0; f < NUM_FREECELLS; ++f) {
        if (state->freecells[f] == nextCard) {
          return true;
        }
      }
    }
  }

  return false;
}

bool containsOnlyKingSeq(const GameState *state, int c, bool verbose) {
  // printf("called containsOnlyKingSeq with c %d\n", c);
  const int seq_len = get_sequence_length(state, c);
  if (verbose) {
    printf("seq_len %d | ", seq_len);
    if (seq_len > 0) {
      uint8_t bottomCard = state->columns[c][0];
      uint8_t rank = card_rank(bottomCard);
      printf("rank of bottom card %d | ", (int)rank);
      printf("bottom card ");
      print_card(bottomCard);
      printf("\n");
    } else {
      printf("\n");
    }
  }
  bool res = seq_len > 0 && seq_len == state->col_lens[c] &&
             card_rank(state->columns[c][0]) == 13;
  // if (res)
  // {
  //     printf("column %d contains only a king seq:", c);
  //     print_game_state(state);
  // }
  // else
  // {
  //     if (c == 0)
  //     {
  //         printf("column 0 does not contain only a king seq?");
  //         print_game_state(state);
  //     }
  // }
  return res;
}

// Does not check, if there are enough free cells and/or columns available.
int fittingColumnDst(GameState *state, uint8_t card) {
  // First, search non-empty column onto which card can be laid.
  // Remember the last visited empty column.
  int empty = -1;
  for (int c = NUM_COLUMNS - 1; c >= 0; --c) {
    if (state->col_lens[c] == 0) {
      empty = c;
    } else {
      if (card + 4 == state->columns[c][state->col_lens[c] - 1])
        return c;
    }
  }

  // Now, if an empty column exists, the lowest one of them is set in empty.
  // Otherwise, empty == -1 which means no column does fit. So return empty
  // here.
  return empty;
}

bool solve(GameState *state, uint8_t depth);

bool tryColToCol(GameState *state, int src, int dst, int seq_len, uint8_t depth,
                 uint8_t top_card_of_group) {
  int sl = seq_len;

  // --- MAKE THE MOVE ---
  int src_start = state->col_lens[src] - sl;
  int dst_start = state->col_lens[dst];
  for (int i = 0; i < sl; i++) {
    state->columns[dst][dst_start + i] = state->columns[src][src_start + i];
    state->columns[src][src_start + i] = 255;
  }
  state->col_lens[src] -= sl;
  state->col_lens[dst] += sl;

  assert(depth < MAX_DEPTH);
  move_history[depth] =
      (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst,
             top_card_of_group,       (uint8_t)sl,  *state};

  bool res = (solve(state, depth + 1));

  // --- BACKTRACK ---
  state->col_lens[src] += sl;
  state->col_lens[dst] -= sl;
  for (int i = 0; i < sl; i++) {
    state->columns[src][src_start + i] = state->columns[dst][dst_start + i];
    state->columns[dst][dst_start + i] = 255;
  }

  return res;
}

bool tryFreecellToCol(GameState *state, int f, int c, uint8_t depth) {
  const uint8_t fc_card = state->freecells[f];
  assert(fc_card >= 0 && fc_card < 52); // so not 255!
  // Make the move
  state->freecells[f] = 255; // CLEAR!
  state->columns[c][state->col_lens[c]] = fc_card;
  state->col_lens[c]++;

  assert(depth < MAX_DEPTH);
  move_history[depth] =
      (Move){MOVE_FREECELL_TO_TABLEAU, f, c, fc_card, 0, *state};

  bool res = (solve(state, depth + 1));

  // Backtrack
  state->col_lens[c]--;
  state->columns[c][state->col_lens[c]] = 255; // CLEAR!
  state->freecells[f] = fc_card;               // RESTORE

  return res;
}

int findFreeCol(GameState *state) {
  for (int c = 0; c < NUM_COLUMNS; ++c) {
    if (state->col_lens[c] == 0)
      return c;
  }
  return -1;
}

bool canColToCol(GameState *state, int src, int dst, int maxMovableOntoEmptyDst,
                 int maxMovableOntoNonEmptyDst, int *p_seq_len,
                 uint8_t *p_top_card_of_group) {
  // Length of the contiguous sequence at the end of src
  *p_seq_len = get_sequence_length(state, src);
  const int seq_len = *p_seq_len;
  if (seq_len == 0)
    return false;
  *p_top_card_of_group = state->columns[src][state->col_lens[src] - seq_len];
  const uint8_t top_card_of_group = *p_top_card_of_group;
  int fittingDst = fittingColumnDst(state, top_card_of_group);
  if (fittingDst != dst)
    return false;
  bool dst_is_empty = (state->col_lens[dst] == 0);

  int empty_cols_count = 0;
  for (int c = 0; c < NUM_COLUMNS; c++) {
    if (state->col_lens[c] == 0)
      empty_cols_count++;
  }

  // int current_empty_cols = empty_cols_count - (dst_is_empty ? 1 : 0);
  // int max_cards = max_movable_cards(free_cells_count, current_empty_cols,
  // dst_is_empty);
  int max_cards =
      dst_is_empty ? maxMovableOntoEmptyDst : maxMovableOntoNonEmptyDst;
  return seq_len <= max_cards;
}

int cmpGameState(const GameState *a, const GameState *b) {
  for (int i = 0; i < NUM_FREECELLS; ++i) {
    if (a->freecells[i] != b->freecells[i]) {
      return (int)a->freecells[i] - (int)b->freecells[i];
    }
  }
  for (int i = 0; i < NUM_COLUMNS; ++i) {
    if (a->col_lens[i] != b->col_lens[i]) {
      return (int)a->col_lens[i] - (int)b->col_lens[i];
    }
    for (int j = 0; j < a->col_lens[i]; ++j) {
      if (a->columns[i][j] != b->columns[i][j]) {
        return (int)a->columns[i][j] - b->columns[i][j];
      }
    }
  }

  // ab hier muessen dann auch die foundations gleich sein, sonst mind. ein game
  // state inkonsistent!

  for (int i = 0; i < 4; ++i) {
    assert(a->foundations[i] == b->foundations[i]);
  }

  return 0;
}

bool dbgCycleInMoveList(GameState *s, int depth) {
  for (int i = 0; i < depth - 1; ++i) {
    if (cmpGameState(&move_history[i].gameState, s) == 0) {
      return true;
    }
  }

  return false;
}

bool statesEqual(GameState *a, GameState *b) {
  for (int i = 0; i < 4; ++i) {
    if (a->foundations[i] != b->foundations[i])
      return false;
  }

  for (int i = 0; i < NUM_FREECELLS; ++i) {
    if (a->freecells[i] != b->freecells[i])
      return false;
  }

  for (int i = 0; i < NUM_COLUMNS; ++i) {
    if (a->col_lens[i] != b->col_lens[i])
      return false;

    for (int j = 0; j < a->col_lens[i]; ++j) {
      if (a->columns[i][j] != b->columns[i][j])
        return false;
    }
  }

  return true;
}

bool solve(GameState *state, uint8_t depth) {

//   if (statesEqual(&bugState, state)) {
//     print_game_state(state);
//     printf("depth %d:\n", (int)depth);
//   }

//   if (statesEqual(&bugState2, state)) {
//     printf("Visited bug state 2:\n");
//     print_game_state(state);
//     printf("Now, debug!\n");
//   }
  // print_game_state(state);

#if 0
    bool cycleInMoveList = dbgCycleInMoveList(state, depth);
#endif

  // Check whether this state is already in the arena/hash table
  int arenaIndex = -1;
  if (is_visited_or_add(state, &arenaIndex, depth)) {
    // if (depthAbortsVerbose)
    // {
    //     printf("Zyklus\n");
    //     print_game_state(state);
    // }
    return false;
  }

  if (visitedBugState) {
    printf("vor is_solved\n");
    print_game_state(state);
  }

  GameState stateBeforeIsSolved = *state;

  if (is_solved(state)) {
    if (memcmp(&stateBeforeIsSolved, state, sizeof(GameState)) != 0) {
      printf("Game state changed during is_solved!. Before:\n");
      print_game_state(&stateBeforeIsSolved);
      printf("After:\n");
      print_game_state(state);
      printf("Damn ;-)\n");
    }
    if (visitedBugState) {
      printf("nach is_solved (true)\n");
      print_game_state(state);
    }
    assert(depth <= bestSolutionDepth);
    assert(depth <= MAX_DEPTH);
    bestSolutionDepth = depth;
    bestSolutionArenaIndex = arenaIndex;
    // print_solution(move_history, depth, false);
    printf("Solution with depth %d\n", depth);
    memcpy(bestMoveHistory, move_history, sizeof(Move) * bestSolutionDepth);

    return true;
  }

  if (visitedBugState) {
    printf("nach is_solved (false)\n");
    print_game_state(state);
  }

#if 0
    if (cycleInMoveList)
    {
        printf("game state\n");
        print_game_state(state);
        print_moves(move_history, depth, false, "current moves at cycle bug");
        printf("\nFEHLER! Zyklus in move list, aber nicht erkannt in is_solved!\n");
        // noch mal is_solved zum debuggen
        // cmp_verbose = true;
        is_visited_or_add(state, &arenaIndex, depth);
        exit(5);
    }
#endif

  // The state of the foundations gives a lower bound for the remaining
  // necessary moves.
  int minSolutionDepth = depth;
  for (int i = 0; i < 4; ++i) {
    minSolutionDepth += (13 - state->foundations[i]);
  }

  if (minSolutionDepth >= bestSolutionDepth) {
    if (depth == MAX_DEPTH)
      printf("\n\nMAX DEPTH - aborting!\n\n");
    // else silent!
    // printf("aborting because cannot be better.\n");

    ++depthAborts;

    // if (depthAborts % 100000 == 0)
    // {
    //     printf("\n>>> SNAPSHOT after %" PRIu64 " aborts (arena: %.2f MB -
    //     %.2f%%) <<<\n",
    //            depthAborts,
    //            (double)arena_offset / (1024.0 * 1024.0),
    //            arena_offset * 100.0 / ARENA_SIZE);
    //     print_game_state(state);
    //     if (bestSolutionDepth < MAX_DEPTH + 1)
    //     {
    //         printf("Shortest known solution: %d moves\n", bestSolutionDepth);
    //     }
    //     else
    //     {
    //         printf("No solution found, yet.\n");
    //     }
    //     print_moves(move_history, depth, false, "Moves of aborted state");
    //     // printf("Moves of aborted state:\n");
    //     // for (int i = 0; i < depth; ++i)
    //     // {
    //     //     print_move(move_history + i);
    //     // }

    //     pause();
    //     // depthAbortsVerbose = true;
    // }

    return false;
  }

  // General info that is always useful and cheap to calculate
  int empty_cols_count = 0;
  for (int c = 0; c < NUM_COLUMNS; c++) {
    if (state->col_lens[c] == 0)
      empty_cols_count++;
  }
  int free_cells_count = 0;
  for (int f = 0; f < NUM_FREECELLS; f++) {
    if (state->freecells[f] == 255)
      free_cells_count++;
  }
  int maxMovableOntoEmptyDst =
      max_movable_cards1(free_cells_count, empty_cols_count, true);
  int maxMovableOntoNonEmptyDst =
      max_movable_cards1(free_cells_count, empty_cols_count, false);

  // =========================================================================
  // 1. AUTO-MOVES (DOMINANCE RULE FOR BAKER'S GAME)
  // =========================================================================

  // Auto-Move: Tableau -> Foundation
  for (int col = 0; col < NUM_COLUMNS; col++) {
    if (state->col_lens[col] > 0) {
      uint8_t card = state->columns[col][state->col_lens[col] - 1];
      uint8_t suit = card & 3;
      uint8_t rank = (card >> 2) + 1;

      if (rank == state->foundations[suit] + 1) {
        // Make the move and clear the slot
        state->foundations[suit]++;
        state->col_lens[col]--;
        state->columns[col][state->col_lens[col]] = 255; // CLEAR!

        assert(depth < MAX_DEPTH);
        move_history[depth] =
            (Move){MOVE_TABLEAU_TO_FOUNDATION, col, suit, card, 0, *state};

        bool res = solve(state, depth + 1);

        // Backtrack
        state->columns[col][state->col_lens[col]] = card; // RESTORE
        state->col_lens[col]++;
        state->foundations[suit]--;

        // if (!searchForBest)
        return res; // HARD CUTOFF!
      }
    }
  }

  // Auto-Move: FreeCell -> Foundation
  for (int f = 0; f < NUM_FREECELLS; f++) {
    if (state->freecells[f] != 255) {
      uint8_t card = state->freecells[f];
      uint8_t suit = card & 3;
      uint8_t rank = (card >> 2) + 1;

      if (rank == state->foundations[suit] + 1) {
        // Make the move
        state->foundations[suit]++;
        state->freecells[f] = 255; // CLEAR!

        assert(depth < MAX_DEPTH);
        move_history[depth] =
            (Move){MOVE_FREECELL_TO_FOUNDATION, f, suit, card, 0, *state};

        bool res = solve(state, depth + 1);

        // Backtrack
        state->freecells[f] = card; // RESTORE
        state->foundations[suit]--;

        // if (!searchForBest)
        return res; // HARD CUTOFF!
      }
    }
  }

  // High prio move: card onto column containing only a sequence starting with a
  // king

  for (int dst = 0; dst < NUM_COLUMNS; ++dst) {
    if (containsOnlyKingSeq(state, dst, false)) {
      uint8_t nextCard = state->columns[dst][state->col_lens[dst] - 1] + 4;

      for (int f = 0; f < NUM_FREECELLS; ++f) {
        if (nextCard == state->freecells[f]) {

          bool res = tryFreecellToCol(state, f, dst, depth);
          if (!searchForBest)
            return res; // HARD CUTOFF!
        }
      }

      for (int c = 0; c < NUM_COLUMNS; ++c) {
        int seq_len;
        uint8_t top_card_of_group;
        if (canColToCol(state, c, dst, maxMovableOntoEmptyDst,
                        maxMovableOntoNonEmptyDst, &seq_len,
                        &top_card_of_group)) {
          assert(c != dst); // Otherwise, there is a bug in canColToCol!
          bool res =
              tryColToCol(state, c, dst, seq_len, depth, top_card_of_group);
          if (!searchForBest)
            return res; // HARD CUTOFF!
        }
      }
    }
  }

  // =========================================================================
  // 2. NORMAL BACKTRACKING (TABLEAU AND FREECELLS)
  // =========================================================================

  // A) Tableau -> Tableau (INCLUDING META-MOVES / SUPERMOVES)
  // Rules:
  // - Not onto empty column if fits on other column.
  // - Never move from a column containing only a king sequence to an empty
  // column

  {

    for (int src = 0; src < NUM_COLUMNS; src++) {
      if (state->col_lens[src] == 0)
        continue;

      // Length of the contiguous sequence at the end of src
      int seq_len = get_sequence_length(state, src);
      uint8_t top_card_of_group =
          state->columns[src][state->col_lens[src] - seq_len];
      int dst2 = fittingColumnDst(state, top_card_of_group);

      // for (int dst = 0; dst < NUM_COLUMNS; dst++)
      if (dst2 != -1) {
        // if (src == dst)
        // continue;

        bool dst_is_empty = (state->col_lens[dst2] == 0);

        // Calculate maximum capacity
        // TODO begin remove
        // int current_empty_cols = empty_cols_count - (dst_is_empty ? 1 : 0);
        // int max_cards = max_movable_cards(free_cells_count,
        // current_empty_cols, dst_is_empty);
        // TODO end remove
        int max_cards =
            dst_is_empty ? maxMovableOntoEmptyDst : maxMovableOntoNonEmptyDst;

        if (dst_is_empty) {
          // DESTINATION COLUMN IS EMPTY:
          // Move only if:
          // 1. The sequence is not already the ENTIRE column (pointless
          // isomorphism move).
          // 2. The sequence is within the max-movable limit.
          // NEW
          // 3. The next-higher card above the highest card of the moved
          // sequence is not also reachable.
          if (seq_len < state->col_lens[src] && seq_len <= max_cards)
            if (tryColToCol(state, src, dst2, seq_len, depth,
                            top_card_of_group))
              if (!searchForBest)
                return true;
        } else {
          // DESTINATION COLUMN IS NOT EMPTY:
          uint8_t dst_card = state->columns[dst2][state->col_lens[dst2] - 1];

          if (seq_len <=
              max_cards) // Makes only sense, if can be moved completely.
          {
            int sl = seq_len;
            uint8_t top_card_of_group =
                state->columns[src][state->col_lens[src] - sl];

            // Baker's Game rule: same suit (same symbol), rank exactly 1 lower.
            // (top_card_of_group + 4) == dst_card
            if ((top_card_of_group + 4) == dst_card) {
              // --- MAKE THE MOVE ---
              int src_start = state->col_lens[src] - sl;
              for (int i = 0; i < sl; i++) {
                state->columns[dst2][state->col_lens[dst2] + i] =
                    state->columns[src][src_start + i];
                state->columns[src][src_start + i] = 255;
              }
              state->col_lens[src] -= sl;
              state->col_lens[dst2] += sl;

              assert(depth < MAX_DEPTH);
              move_history[depth] =
                  (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst2,
                         top_card_of_group,       (uint8_t)sl,  *state};

              if (solve(state, depth + 1)) {
                if (!searchForBest)
                  return true;
              }

              // --- BACKTRACK ---
              state->col_lens[dst2] -= sl;
              state->col_lens[src] += sl;
              for (int i = 0; i < sl; i++) {
                state->columns[src][src_start + i] =
                    state->columns[dst2][state->col_lens[dst2] + i];
                state->columns[dst2][state->col_lens[dst2] + i] = 255;
              }
            }
          }

          // If the actions above were not successful, we have to check the move
          // onto a free column, if there is any.
          dst2 = findFreeCol(state);

          if (dst2 != -1) {
            // DESTINATION COLUMN IS EMPTY:
            // Move only if:
            // 1. The sequence is not already the ENTIRE column (pointless
            // isomorphism move).
            // 2. The sequence is within the max-movable limit.
            // NEW
            // 3. The next-higher card above the highest card of the moved
            // sequence is not also reachable.
            if (seq_len < state->col_lens[src] && seq_len <= maxMovableOntoEmptyDst)
              if (tryColToCol(state, src, dst2, seq_len, depth,
                              top_card_of_group))
                if (!searchForBest)
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
    for (int f = 0; f < NUM_FREECELLS; f++) {
      if (state->freecells[f] == 255) {
        free_indices[free_cells_count++] = f;
      }
    }

    if (free_cells_count > 0) {
      for (int src = 0; src < NUM_COLUMNS; src++) {
        int len = state->col_lens[src];
        if (len == 0)
          continue;

        int seq_len = get_sequence_length(state, src);

        // CASE 1: Place a single card (seq_len == 1) into a FreeCell
        if (seq_len == 1) {
          int f_slot = free_indices[0];
          uint8_t card = state->columns[src][len - 1];
          // war nur zum debuggen:
          // const char *suit = suits[card & 3];
          // const char *rank = ranks[card >> 2];

          state->freecells[f_slot] = card;
          state->columns[src][len - 1] = 255;
          state->col_lens[src]--;

          assert(depth < MAX_DEPTH);
          move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL,
                                       (uint8_t)src,
                                       (uint8_t)f_slot,
                                       card,
                                       1,
                                       *state};
          // Debugging: ab Zug Column 5   -> FreeCell 1 verbose, wenn dadurch
          // Spalte 5 leer wird if (!cmp_verbose && len == 1 && src == 4 &&
          // f_slot == 0 && card == make_card(5, HEARTS))
          // {
          //     cmp_verbose = true;
          //     print_game_state(state);
          //     print_move(move_history + depth);
          //     printf("Ab jetzt VERBOSE!\n");
          //     pause();
          // }

          if (solve(state, depth + 1)) {
            if (!searchForBest)
              return true;
          }

          // Backtrack
          state->col_lens[src]++;
          state->columns[src][len - 1] = card;
          state->freecells[f_slot] = 255;
        }
        // CASE 2: Atomic meta-move - evacuate an ENTIRE sequence into FreeCells
        else if (seq_len > 1 && seq_len <= free_cells_count && len > seq_len) {
          // Place ALL seq_len cards of the sequence into FreeCells at once
          // in order to expose the non-sequence card UNDERNEATH.
          uint8_t card;
          // MAKE THE MOVE
          for (int i = 0; i < seq_len; i++) {
            card = state->columns[src][len - 1 - i];
            int f_slot = free_indices[i];
            state->freecells[f_slot] = card;
            state->columns[src][len - 1 - i] = 255;
          }
          state->col_lens[src] -= seq_len;

          // Record it in the history (e.g. count = seq_len)
          assert(depth < MAX_DEPTH);
          move_history[depth] = (Move){MOVE_TABLEAU_TO_FREECELL, (uint8_t)src,
                                       (uint8_t)free_indices[0], card,
                                       (uint8_t)seq_len,         *state};

          if (solve(state, depth + 1)) {
            if (!searchForBest)
              return true;
          }

          // BACKTRACK
          state->col_lens[src] += seq_len;
          for (int i = seq_len - 1; i >= 0; i--) {
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

    for (int f = 0; f < NUM_FREECELLS; f++) {
      if (state->freecells[f] == 255 || seqInFreecells(state, f))
        continue;

      uint8_t fc_card = state->freecells[f];
      int dst = fittingColumnDst(state, fc_card);
      if (dst != -1) {
        if (tryFreecellToCol(state, f, dst, depth)) {
          if (!searchForBest)
            return true;
        }
      }
    }
  }

  // printf("No move in depth %d\n", depth);
  // print_game_state(state);

//   if (cmpGameState(&stateBeforeIsSolved, state) != 0) {
//     printf("Game state changed during solve(). Before:\n");
//     print_game_state(&stateBeforeIsSolved);
//     printf("After:\n");
//     print_game_state(state);
//     printf("Damn ;-)\n");
//   }

  return false;
}

// Maximum total capacity for evacuating / breaking up a sequence (FreeCells +
// empty columns)
static inline int max_evacuable_cards(int free_cells, int empty_cols) {
  if (empty_cols == 0)
    return free_cells;
  return ((free_cells + 1) * (1 << empty_cols) - 1) + free_cells;
}

// --- PRINT FUNCTIONS ---

void pause() {
  int c;
  while ((c = getchar()) != '\n' && c != EOF)
    ;
}

void print_move(const Move *pm) {
  switch (pm->type) {
  case MOVE_TABLEAU_TO_FOUNDATION:
    printf("Column %d   -> Foundation  [", pm->src + 1);
    print_card(pm->card);
    printf("]\n");
    break;
  case MOVE_FREECELL_TO_FOUNDATION:
    printf("FreeCell %d -> Foundation  [", pm->src + 1);
    print_card(pm->card);
    printf("]\n");
    break;
  case MOVE_TABLEAU_TO_TABLEAU:
    printf("Column %d   -> Column %d     [", pm->src + 1, pm->dst + 1);
    print_card(pm->card);
    printf("]\n");
    break;
  case MOVE_TABLEAU_TO_FREECELL:
    printf("Column %d   -> FreeCell %d   [", pm->src + 1, pm->dst + 1);
    print_card(pm->card);
    printf("]\n");
    break;
  case MOVE_FREECELL_TO_TABLEAU:
    printf("FreeCell %d -> Column %d     [", pm->src + 1, pm->dst + 1);
    print_card(pm->card);
    printf("]\n");
    break;
  }
}
void print_moves(const Move *move_history, int numMoves, bool interactive,
                 const char *header) {
  printf("\n====================================\n");
  // printf(" SOLUTION FOUND IN %d MOVES:\n", numMoves);
  printf("%s\n", header);
  printf("====================================\n\n");

  assert(numMoves < MAX_DEPTH);
  for (int i = 0; i < numMoves; i++) {
    Move m = move_history[i];
    printf("Move %3d: ", i + 1);
    print_move(&m);

    print_game_state(&m.gameState);
    printf("Press Enter to continue ");
    fflush(stdout);
    if (interactive)
      pause();
  }
  printf("\n");
}

// Reads cards in the format "p k", "pk", "kr 10", "h,2", "k;a", and so on.
int parse_card(const char *suit_str, const char *rank_str, uint8_t *out_card) {
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
  else {
    int r = atoi(rank_str);
    if (r >= 2 && r <= 10)
      rank = (uint8_t)r;
    else
      return -1;
  }

  *out_card = make_card(rank, suit);
  return 0;
}

bool validate_deck(const GameState *game) {
  bool seen[52] = {false};
  int card_count = 0;

  // 1. Count and mark cards in the tableau
  for (int col = 0; col < NUM_COLUMNS; col++) {
    for (int i = 0; i < game->col_lens[col]; i++) {
      uint8_t card = game->columns[col][i];

      if (card >= 52) {
        printf("\nError: Invalid card value (%d) found!\n", card);
        return false;
      }

      if (seen[card]) {
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
  if (card_count != 52) {
    printf("\nError: Only %d of 52 cards were read!\n", card_count);
    printf("The following cards are MISSING:\n");

    for (int i = 0; i < 52; i++) {
      if (!seen[i]) {
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

bool parse_board_from_file(GameState *out_game, FILE *f) {
  memset(out_game, 0, sizeof(GameState));
  memset(out_game->freecells, 255, 4);

  char line_buf[512];
  int current_col = 0;

  printf("--- Please enter the board (8 columns) ---\n");

  while (current_col < 8 && fgets(line_buf, sizeof(line_buf), f)) {
    char *l = line_buf;
    while (isspace(*l))
      l++;

    if (*l == '\0' || *l == '#')
      continue;

    if (strncmp(l, "-", 1) == 0) {
      out_game->col_lens[current_col++] = 0;
      printf("Column %d read (0 cards - empty)\n", current_col);
      continue;
    }

    char *ptr = l;
    while (*ptr && out_game->col_lens[current_col] < 19) {
      // Skip whitespace, commas, and semicolons
      while (*ptr && (isspace(*ptr) || *ptr == ',' || *ptr == ';'))
        ptr++;
      if (*ptr == '\0')
        break;

      // Read the suit
      char suit_buf[8] = {0};
      int s_idx = 0;
      while (*ptr && isalpha(*ptr) && s_idx < 7) {
        suit_buf[s_idx++] = (char)tolower(*ptr++);
      }

      // Skip whitespace between suit and rank
      while (*ptr && isspace(*ptr))
        ptr++;

      // Read the rank
      char rank_buf[8] = {0};
      int r_idx = 0;
      while (*ptr && isalnum(*ptr) && r_idx < 7) {
        rank_buf[r_idx++] = (char)tolower(*ptr++);
      }

      if (s_idx == 0 || r_idx == 0) {
        printf("\nError: Incomplete card in column %d near '%s'\n",
               current_col + 1, ptr);
        return false;
      }

      uint8_t card;
      if (parse_card(suit_buf, rank_buf, &card) == 0) {
        uint8_t len = out_game->col_lens[current_col];
        out_game->columns[current_col][len] = card;
        out_game->col_lens[current_col]++;
      } else {
        printf("\nError: Invalid card '%s %s' in column %d!\n", suit_buf,
               rank_buf, current_col + 1);
        return false;
      }
    }

    printf("Column %d read (%d cards)\n", current_col + 1,
           out_game->col_lens[current_col]);
    current_col++;
  }

  if (current_col < 8) {
    printf("\nError: Only %d of 8 columns were read!\n", current_col);
    return false;
  }

  // Always check that the deck is complete (exactly 52 unique cards)!
  return validate_deck(out_game);
}

void print_card(uint8_t card) {

  if (card == 255) {
    printf("----");
    return;
  }
  uint8_t suit = card & 3;
  uint8_t rank = card >> 2;
  if (suit == 1 || suit == 2) {
    printf("%s", ANSI_ROT);
  }
  printf("%s %s", suits[suit], ranks[rank]);
  if (suit == 1 || suit == 2) {
    printf("%s", ANSI_RESET);
  }
}

void print_game_state(const GameState *s) {
  printf("\n===================================== CURRENT STATE "
         "=====================================\n");

  // 1. Foundations & FreeCells
  printf("FreeCells:   ");
  for (int f = 0; f < NUM_FREECELLS; f++) {
    printf("[");
    print_card(s->freecells[f]);
    printf("] ");
  }
  printf("      Foundations: ");
  // const char *suits[] = {"Spades", "Hearts", "Diamonds", "Clubs"};
  for (int i = 0; i < 4; i++) {
    if (s->foundations[i] == 0) {
      if (i == 1 || i == 2) {
        printf(ANSI_ROT);
      }
      printf("[%s --] ", suits[i]);
      if (i == 1 || i == 2) {
        printf(ANSI_RESET);
      }
    } else {
      uint8_t card = make_card(s->foundations[i], i);
      printf("[");
      print_card(card);
      printf("] ");
    }
  }

  printf("\n-------------------------------------------------------------------"
         "----------------------\n");

  // 2. Determine the maximum tableau height
  int max_len = 0;
  for (int col = 0; col < NUM_COLUMNS; col++) {
    if (s->col_lens[col] > max_len)
      max_len = s->col_lens[col];
  }

  // Column headers (exactly 12 characters wide per column)
  for (int col = 0; col < NUM_COLUMNS; col++) {
    char header[16];
    snprintf(header, sizeof(header), "Column %d", col + 1);
    printf("%-10s", header);
  }
  printf("\n");

  // Print the tableau row by row, top to bottom
  for (int row = 0; row < max_len; row++) {
    for (int col = 0; col < NUM_COLUMNS; col++) {
      if (row < s->col_lens[col]) {
        uint8_t card = s->columns[col][row];

        // Format the card into a string first
        // Scratch buffer for a print_card equivalent:
        // const char *suit_names[] = {"Spades", "Hearts", "Diamonds", "Clubs"};
        // war nur zum Debuggen:
        // const char *rank_names[] = {"--", "A", "2", "3", "4", "5", "6", "7",
        // "8", "9", "10", "J", "Q", "K"};

        // war nur zum Debuggen:
        // uint8_t suit = card & 3;
        // uint8_t rank = (card >> 2) + 1;

        print_card(card);
        printf("      ");
      } else {
        printf("%-10s", ""); // Empty cell
      }
    }
    printf("\n");
  }

#if 0
    bool ksFound = false;
    for (int c = 0; c < NUM_COLUMNS; ++c)
    {
        if (containsOnlyKingSeq(s, c, true))
        {
            printf("Column %d contains only a king seq.\n", c + 1);
            ksFound = true;
        }
    }
    if (!ksFound)
    {
        printf("No column contains only a king seq.\n");
    }
#endif
  printf("====================================================================="
         "====================\n\n");
}

static void print_usage(FILE *out, const char *prog) {
  fprintf(
      out,
      "Usage: %s [OPTION] [FILE]\n"
      "\n"
      "Solver for Baker's Game.\n"
      "\n"
      "Reads a board with 8 columns. Without FILE, input is read from standard "
      "input.\n"
      "FILE is used only if it is a regular file; otherwise stdin is read.\n"
      "\n"
      "Options:\n"
      "  -h, -?, --help    display this help and exit\n"
      "\n"
      "Board:\n"
      "  One line per column. Cards for example as \"p k\", \"h,2\", \"kr "
      "10\".\n"
      "  Suits: p (spades), h (hearts), k (diamonds), kr (clubs).\n"
      "  Ranks: a, 2-10, j, q, k. A line \"-\" is an empty column.\n"
      "  Lines starting with # are ignored.\n",
      prog);
}

void allocateMem() {
  arena_buffer = mmap(NULL, ARENA_SIZE, PROT_READ | PROT_WRITE,
                      MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);

  if (arena_buffer == MAP_FAILED) {
    perror("mmap failed for arena_buffer");
    exit(EXIT_FAILURE);
  }

  // // 2. Speicher im physischen RAM festpinnen (verhindert Swapping komplett)
  // if (mlock(arena_buffer, ARENA_SIZE) != 0)
  // {
  //     perror("mlock fehlgeschlagen (Fehlen evtl. RLIMIT_MEMLOCK Rechte?)");
  //     munmap(arena_buffer, ARENA_SIZE);
  //     exit(EXIT_FAILURE);
  // }

  hash_buckets =
      mmap(NULL, HASH_TABLE_SIZE * sizeof(uint64_t), PROT_READ | PROT_WRITE,
           MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);

  if (hash_buckets == MAP_FAILED) {
    perror("mmap failed for hash_buckets");
    munmap(arena_buffer, ARENA_SIZE);
    exit(EXIT_FAILURE);
  }

  // 2. Speicher im physischen RAM festpinnen (verhindert Swapping komplett)
  if (mlock(hash_buckets, HASH_TABLE_SIZE * sizeof(uint64_t)) != 0) {
    perror("mlock fehlgeschlagen (Fehlen evtl. RLIMIT_MEMLOCK Rechte?)");
    munmap(hash_buckets, HASH_TABLE_SIZE * sizeof(uint64_t));
    munmap(arena_buffer, ARENA_SIZE);
    exit(EXIT_FAILURE);
  }
}

void freeMem() {
  munmap(hash_buckets, HASH_TABLE_SIZE * sizeof(uint64_t));
  munmap(arena_buffer, ARENA_SIZE);
}

void setBugState() {
  bugState.foundations[0] = 12;
  bugState.foundations[1] = 1;
  bugState.foundations[2] = 2;
  bugState.foundations[3] = 0;
  enum { P, H, K, KR };
  bugState.freecells[0] = make_card(9, H);
  bugState.freecells[1] = make_card(4, H);
  bugState.freecells[2] = 255;
  bugState.freecells[3] = make_card(11, H);

  bugState.col_lens[0] = 7;
  bugState.columns[0][0] = make_card(1, KR);
  bugState.columns[0][1] = make_card(6, K);
  bugState.columns[0][2] = make_card(13, P);
  bugState.columns[0][3] = make_card(10, H);
  bugState.columns[0][4] = make_card(10, KR);
  bugState.columns[0][5] = make_card(2, H);
  bugState.columns[0][6] = make_card(13, K);

  bugState.col_lens[1] = 5;
  bugState.columns[1][0] = make_card(7, KR);
  bugState.columns[1][1] = make_card(13, KR);
  bugState.columns[1][2] = make_card(13, H);
  bugState.columns[1][3] = make_card(3, KR);
  bugState.columns[1][4] = make_card(2, KR);

  bugState.col_lens[2] = 7;
  bugState.columns[2][0] = make_card(5, K);
  bugState.columns[2][1] = make_card(8, KR);
  bugState.columns[2][2] = make_card(3, H);
  bugState.columns[2][3] = make_card(12, K);
  bugState.columns[2][4] = make_card(11, K);
  bugState.columns[2][5] = make_card(10, K);
  bugState.columns[2][6] = make_card(9, K);

  bugState.col_lens[3] = 8;
  bugState.columns[3][0] = make_card(11, KR);
  bugState.columns[3][1] = make_card(8, H);
  bugState.columns[3][2] = make_card(12, H);
  bugState.columns[3][3] = make_card(4, K);
  bugState.columns[3][4] = make_card(3, K);
  bugState.columns[3][5] = make_card(6, KR);
  bugState.columns[3][6] = make_card(5, KR);
  bugState.columns[3][7] = make_card(4, KR);

  bugState.col_lens[4] = 4;
  bugState.columns[4][0] = make_card(5, H);
  bugState.columns[4][1] = make_card(9, KR);
  bugState.columns[4][2] = make_card(8, K);
  bugState.columns[4][3] = make_card(7, K);

  bugState.col_lens[5] = 0;

  bugState.col_lens[6] = 2;
  bugState.columns[6][0] = make_card(7, H);
  bugState.columns[6][1] = make_card(6, H);

  bugState.col_lens[7] = 1;
  bugState.columns[7][0] = make_card(12, KR);

  packedBugStateLen = pack_state((&bugState), packedBugState);



  bugState2.foundations[0] = 12;
  bugState2.foundations[1] = 1;
  bugState2.foundations[2] = 2;
  bugState2.foundations[3] = 0;
//   enum { P, H, K, KR };
  bugState2.freecells[0] = make_card(9, H);
  bugState2.freecells[1] = make_card(4, H);
  bugState2.freecells[2] = 255;
  bugState2.freecells[3] = make_card(11, H);

  bugState2.col_lens[0] = 7;
  bugState2.columns[0][0] = make_card(1, KR);
  bugState2.columns[0][1] = make_card(6, K);
  bugState2.columns[0][2] = make_card(13, P);
  bugState2.columns[0][3] = make_card(10, H);
  bugState2.columns[0][4] = make_card(10, KR);
  bugState2.columns[0][5] = make_card(2, H);
  bugState2.columns[0][6] = make_card(13, K);

  bugState2.col_lens[1] = 5;
  bugState2.columns[1][0] = make_card(7, KR);
  bugState2.columns[1][1] = make_card(13, KR);
  bugState2.columns[1][2] = make_card(13, H);
  bugState2.columns[1][3] = make_card(3, KR);
  bugState2.columns[1][4] = make_card(2, KR);

  bugState2.col_lens[2] = 3;
  bugState2.columns[2][0] = make_card(5, K);
  bugState2.columns[2][1] = make_card(8, KR);
  bugState2.columns[2][2] = make_card(3, H);

  bugState2.col_lens[3] = 8;
  bugState2.columns[3][0] = make_card(11, KR);
  bugState2.columns[3][1] = make_card(8, H);
  bugState2.columns[3][2] = make_card(12, H);
  bugState2.columns[3][3] = make_card(4, K);
  bugState2.columns[3][4] = make_card(3, K);
  bugState2.columns[3][5] = make_card(6, KR);
  bugState2.columns[3][6] = make_card(5, KR);
  bugState2.columns[3][7] = make_card(4, KR);

  bugState2.col_lens[4] = 4;
  bugState2.columns[4][0] = make_card(5, H);
  bugState2.columns[4][1] = make_card(9, KR);
  bugState2.columns[4][2] = make_card(8, K);
  bugState2.columns[4][3] = make_card(7, K);

  bugState2.col_lens[5] = 4;
  bugState2.columns[5][0] = make_card(12, K);
  bugState2.columns[5][1] = make_card(11, K);
  bugState2.columns[5][2] = make_card(10, K);
  bugState2.columns[5][3] = make_card(9, K);

  bugState2.col_lens[6] = 2;
  bugState2.columns[6][0] = make_card(7, H);
  bugState2.columns[6][1] = make_card(6, H);

  bugState2.col_lens[7] = 1;
  bugState2.columns[7][0] = make_card(12, KR);
}

void testBug() {
  GameState bugState;
  bugState.foundations[0] = 12;
  bugState.foundations[1] = 1;
  bugState.foundations[2] = 2;
  bugState.foundations[3] = 0;
  enum { P, H, K, KR };
  bugState.freecells[0] = make_card(9, H);
  bugState.freecells[1] = make_card(4, H);
  bugState.freecells[2] = 255;
  bugState.freecells[3] = make_card(11, H);

  bugState.col_lens[0] = 7;
  bugState.columns[0][0] = make_card(1, KR);
  bugState.columns[0][1] = make_card(6, K);
  bugState.columns[0][2] = make_card(13, P);
  bugState.columns[0][3] = make_card(10, H);
  bugState.columns[0][4] = make_card(10, KR);
  bugState.columns[0][5] = make_card(2, H);
  bugState.columns[0][6] = make_card(13, K);

  bugState.col_lens[1] = 5;
  bugState.columns[1][0] = make_card(7, KR);
  bugState.columns[1][1] = make_card(13, KR);
  bugState.columns[1][2] = make_card(13, H);
  bugState.columns[1][3] = make_card(3, KR);
  bugState.columns[1][4] = make_card(2, KR);

  bugState.col_lens[2] = 7;
  bugState.columns[2][0] = make_card(5, K);
  bugState.columns[2][1] = make_card(8, KR);
  bugState.columns[2][2] = make_card(3, H);
  bugState.columns[2][3] = make_card(12, K);
  bugState.columns[2][4] = make_card(11, K);
  bugState.columns[2][5] = make_card(10, K);
  bugState.columns[2][6] = make_card(9, K);

  bugState.col_lens[3] = 8;
  bugState.columns[3][0] = make_card(11, KR);
  bugState.columns[3][1] = make_card(8, H);
  bugState.columns[3][2] = make_card(12, H);
  bugState.columns[3][3] = make_card(4, K);
  bugState.columns[3][4] = make_card(3, K);
  bugState.columns[3][5] = make_card(6, KR);
  bugState.columns[3][6] = make_card(5, KR);
  bugState.columns[3][7] = make_card(4, KR);

  bugState.col_lens[4] = 4;
  bugState.columns[4][0] = make_card(5, H);
  bugState.columns[4][1] = make_card(9, KR);
  bugState.columns[4][2] = make_card(8, K);
  bugState.columns[4][3] = make_card(7, K);

  bugState.col_lens[5] = 0;

  bugState.col_lens[6] = 2;
  bugState.columns[6][0] = make_card(7, H);
  bugState.columns[6][1] = make_card(6, H);

  bugState.col_lens[7] = 1;
  bugState.columns[7][0] = make_card(12, KR);
  print_game_state((&bugState));

  GameState *state = &bugState;

  int empty_cols_count = 0;
  for (int c = 0; c < NUM_COLUMNS; c++) {
    if (state->col_lens[c] == 0)
      empty_cols_count++;
  }
  int free_cells_count = 0;
  for (int f = 0; f < NUM_FREECELLS; f++) {
    if (state->freecells[f] == 255)
      free_cells_count++;
  }
  int maxMovableOntoEmptyDst =
      max_movable_cards1(free_cells_count, empty_cols_count, true);
  int maxMovableOntoNonEmptyDst =
      max_movable_cards1(free_cells_count, empty_cols_count, false);

  printf("maxMovableOntoEmptyDst=%d\n", maxMovableOntoEmptyDst);
  printf("maxMovableOntoNonEmptyDst=%d\n", maxMovableOntoNonEmptyDst);

  int depth = 0;

  {
    int src = 2;

    // Length of the contiguous sequence at the end of src
    int seq_len = get_sequence_length(state, src);
    uint8_t top_card_of_group =
        state->columns[src][state->col_lens[src] - seq_len];
    int dst2 = fittingColumnDst(state, top_card_of_group);

    // for (int dst = 0; dst < NUM_COLUMNS; dst++)
    if (dst2 != -1) {
      // if (src == dst)
      // continue;

      bool dst_is_empty = (state->col_lens[dst2] == 0);

      // Calculate maximum capacity
      // TODO begin remove
      // int current_empty_cols = empty_cols_count - (dst_is_empty ? 1 : 0);
      // int max_cards = max_movable_cards(free_cells_count,
      // current_empty_cols, dst_is_empty);
      // TODO end remove
      int max_cards =
          dst_is_empty ? maxMovableOntoEmptyDst : maxMovableOntoNonEmptyDst;

      if (dst_is_empty) {
        // DESTINATION COLUMN IS EMPTY:
        // Move only if:
        // 1. The sequence is not already the ENTIRE column (pointless
        // isomorphism move).
        // 2. The sequence is within the max-movable limit.
        // NEW
        // 3. The next-higher card above the highest card of the moved
        // sequence is not also reachable.
        if (seq_len < state->col_lens[src] && seq_len <= max_cards)
          if (tryColToCol(state, src, dst2, seq_len, depth, top_card_of_group))
            if (!searchForBest)
              return;
      } else {
        // DESTINATION COLUMN IS NOT EMPTY:
        uint8_t dst_card = state->columns[dst2][state->col_lens[dst2] - 1];

        if (seq_len <=
            max_cards) // Makes only sense, if can be moved completely.
        {
          int sl = seq_len;
          uint8_t top_card_of_group =
              state->columns[src][state->col_lens[src] - sl];

          // Baker's Game rule: same suit (same symbol), rank exactly 1 lower.
          // (top_card_of_group + 4) == dst_card
          if ((top_card_of_group + 4) == dst_card) {
            // --- MAKE THE MOVE ---
            int src_start = state->col_lens[src] - sl;
            for (int i = 0; i < sl; i++) {
              state->columns[dst2][state->col_lens[dst2] + i] =
                  state->columns[src][src_start + i];
              state->columns[src][src_start + i] = 255;
            }
            state->col_lens[src] -= sl;
            state->col_lens[dst2] += sl;

            assert(depth < MAX_DEPTH);
            move_history[depth] =
                (Move){MOVE_TABLEAU_TO_TABLEAU, (uint8_t)src, (uint8_t)dst2,
                       top_card_of_group,       (uint8_t)sl,  *state};

            if (solve(state, depth + 1)) {
              if (!searchForBest)
                return;
            }

            // --- BACKTRACK ---
            state->col_lens[dst2] -= sl;
            state->col_lens[src] += sl;
            for (int i = 0; i < sl; i++) {
              state->columns[src][src_start + i] =
                  state->columns[dst2][state->col_lens[dst2] + i];
              state->columns[dst2][state->col_lens[dst2] + i] = 255;
            }
          }
        }

        // If the actions above were not successful, we have to check the move
        // onto a free column, if there is any.
        dst2 = findFreeCol(state);

        if (dst2 != -1) {
          // DESTINATION COLUMN IS EMPTY:
          // Move only if:
          // 1. The sequence is not already the ENTIRE column (pointless
          // isomorphism move).
          // 2. The sequence is within the max-movable limit.
          // NEW
          // 3. The next-higher card above the highest card of the moved
          // sequence is not also reachable.
          if (seq_len < state->col_lens[src] && seq_len <= max_cards)
            if (tryColToCol(state, src, dst2, seq_len, depth,
                            top_card_of_group))
              if (!searchForBest)
                return;
        }
      }
    }
  }
}

int main(int argc, char **argv) {
  const char *prog = (argc > 0 && argv[0] && argv[0][0]) ? argv[0] : "main3";

  // TODO BEGIN remove me after testing
  setBugState();
  // TODO END remove me after testing

  //   testBug();
  //   return -1;

  if (argc >= 2 && (strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "-?") == 0 ||
                    strcmp(argv[1], "--help") == 0)) {
    print_usage(stdout, prog);
    return 0;
  }

  // arena_buffer = calloc(ARENA_SIZE, 1);
  // hash_buckets = calloc(HASH_TABLE_SIZE, sizeof(uint32_t));
  // if (!arena_buffer || !hash_buckets)
  // {
  //     fprintf(stderr, "Could not allocate memory.\n");
  //     return 1;
  // }
  printf("Allocate memory on heap...\n");
  allocateMem();
  printf("Zero arena_buffer...\n");
  memset(arena_buffer, 0, ARENA_SIZE);
  printf("Zero hash_buckets...\n");
  memset(hash_buckets, 0, HASH_TABLE_SIZE * sizeof(uint32_t));
  printf("Done.\n");

  GameState game;
  FILE *input = stdin;
  bool close_input = false;

  if (argc == 2) {
    struct stat st;
    if (stat(argv[1], &st) == 0 && S_ISREG(st.st_mode)) {
      input = fopen(argv[1], "r");
      if (!input) {
        fprintf(stderr, "Could not open file '%s'.\n", argv[1]);
        freeMem();
        return 1;
      }
      close_input = true;
    }
  }

  if (!parse_board_from_file(&game, input)) {
    fprintf(stderr, "\nError while reading input! Aborting.\n");
    if (close_input)
      fclose(input);
    freeMem();
    return 1;
  }

  if (close_input)
    fclose(input);

  printf("\nSearching for a solution for the loaded board...\n");
  print_game_state(&game);

  if (searchForBest) {
    solve(&game, 0);
    dumpCounts();
    printf("%f%% of the arena has been used.\n",
           arena_offset * 100.0 / ARENA_SIZE);
    if (bestSolutionDepth == MAX_DEPTH + 1) {
      printf("No solution found.\n");
    } else {
      printf("\nFound a solution with %d moves.\n", bestSolutionDepth);
      print_moves(bestMoveHistory, bestSolutionDepth, true, "Solution");
    }
  } else {
    bool res = solve(&game, 0);
    dumpCounts();
    printf("%f%% of the arena has been used.\n",
           arena_offset * 100.0 / ARENA_SIZE);
    if (res) {
      printf("Solution in %d moves\n", bestSolutionDepth);
      print_moves(bestMoveHistory, bestSolutionDepth, true, "Solution");
    } else {
      printf("No solution found.\n");
    }
  }

  printf("Unique states in RAM: %" PRId64 " bytes used in the arena.\n",
         arena_offset);
  printf("steps %" PRIu64 "\n", steps);

  freeMem();
  return 0;
}
