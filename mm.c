/*
 * In this implementation i used doubly linked list to represent free blocks
 * pointers to prev and next blocks are stored relative to heap_start
 * thanks to which they can be stored on 4 bytes each
 * used blocks store all info on header.
 * blocks are selected using best fit
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define CHUNKSIZE                                                              \
  (1 << 8) /* Extending heap by this amount (bytes) works                      \
              best*/

typedef int32_t word_t;

typedef enum {
  FREE = 0,
  USED = 1,
  PREVFREE = 2,
} bt_flags;

static word_t *heap_start;
static word_t *heap_end;
static word_t *last;

static word_t *free_list; /* address of first block relative to heap_start */

/* ------------ blocks handling  names are self explainatory -------------- */
static inline bool bt_used(word_t *bt) {
  return *bt & USED;
}
static inline bool bt_free(word_t *bt) {
  return !bt_used(bt);
}
static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}
static inline word_t *bt_header(word_t *bt) {
  return bt;
}
static inline void bt_set_size(word_t *bt, word_t size) {
  *bt = (*bt & 0x3) | size;
  if (!bt_used(bt))
    *bt_footer(bt) = (*bt & 0x3) | size;
}
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}
static inline void bt_clr_prevfree(word_t *bt) {
  *bt &= ~PREVFREE;
  if (!bt_used(bt))
    *bt_footer(bt) &= ~PREVFREE;
}
static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
  if (!bt_used(bt))
    *bt_footer(bt) |= PREVFREE;
}
static inline word_t *bt_next(word_t *addr) {
  return (void *)heap_start + *(addr + 2);
}
static inline void bt_set_next(word_t *addr, word_t *next) {
  word_t *next_addr = addr + 2;
  *next_addr = (void *)next - (void *)heap_start;
}
static inline word_t *bt_prev(word_t *addr) {
  return (void *)heap_start + *(addr + 1);
}
static inline void bt_set_prev(word_t *addr, word_t *prev) {
  word_t *prev_addr = addr + 1;
  *prev_addr = (void *)prev - (void *)heap_start;
}
static inline word_t *bt_physical_next(word_t *addr) {
  return (void *)addr + bt_size(addr);
}
/*assume prevfree is set to true*/
static inline word_t *bt_physical_prev(word_t *addr) {
  word_t size_prev = bt_size(addr - 1);
  return (void *)addr - size_prev;
}
/*set header and footer to size and free tag*/
static inline void bt_set_boundaries_free(word_t *bt) {
  *bt = *bt & ~(0x1);
  if (!bt_used(bt))
    *bt_footer(bt) = *bt & ~(0x1);
}
static inline void bt_set_boundaries_used(word_t *bt) {
  *bt = *bt | 0x1;
}
/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}
/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *bt) {
  return (word_t *)bt - 1;
}
static inline word_t *bt_incr_addr(word_t *bt, word_t amnt) {
  return (void *)bt + amnt;
}
static inline void bt_set_boundaries(word_t *bt, word_t size, bool free,
                                     bool prev_free) {
  bt_set_size(bt, size);
  if (free)
    bt_set_boundaries_free(bt);
  else
    bt_set_boundaries_used(bt);
  if (prev_free)
    bt_set_prevfree(bt);
  else
    bt_clr_prevfree(bt);
}

/* ------------------ linked list related ---------------------*/
static inline void list_remove(word_t *node) {
  if (bt_next(node) == node && bt_prev(node) == node) {
    free_list = NULL;
    return;
  }
  if (free_list == node)
    free_list = bt_next(node);

  word_t *prev = bt_prev(node);
  word_t *next = bt_next(node);

  bt_set_next(prev, next);
  bt_set_prev(next, prev);
}

/* FIFO */
static inline void insert(word_t *block) {
  if (!free_list) {
    free_list = block;
    bt_set_next(block, block);
    bt_set_prev(block, block);
    return;
  }
  word_t *next = free_list;
  word_t *prev = bt_prev(next);

  bt_set_next(prev, block);
  bt_set_prev(next, block);

  bt_set_prev(block, prev);
  bt_set_next(block, next);

  free_list = block;
}

/*try to merge with physical neighbouring blocks if they are free, return new
 * block*/
static inline word_t *merge(word_t *addr) {
  bool prev_free = bt_get_prevfree(addr);
  bool next_free = false;

  word_t *next;
  if (addr < last) {
    next = bt_physical_next(addr);
    next_free = bt_free(next);
  }
  if (next_free) {
    if (last == next)
      last = addr;

    /* what if not on the list? but then shouldn't be set as free*/
    list_remove(next);

    word_t size = bt_size(next) + bt_size(addr);
    bt_set_boundaries(addr, size, true, false);
  }

  if (prev_free) {
    word_t *prev = bt_physical_prev(addr);

    if (last == addr)
      last = prev;
    list_remove(prev);
    word_t size = bt_size(prev) + bt_size(addr);
    addr = prev;
    bt_set_boundaries(addr, size, true, false);
  }
  return addr;
}

/* cut from start asume correct sizes */
/* reutrn new_node set as used, to allocator, put rest on free list */
static inline word_t *get_block(word_t *addr, word_t sz) {
  word_t old_size = bt_size(addr);
  word_t diff = old_size - sz;
  bool prev_free = bt_get_prevfree(addr);
  if (addr < last)
    bt_clr_prevfree(bt_physical_next(addr));
  /* free space less than < 16 return full block to caller */
  if (diff < 16) {
    bt_set_boundaries(addr, old_size, false, prev_free);
    last = MAX(addr, last);
    return addr;
  }
  word_t *new_node = addr;
  bt_set_boundaries(new_node, sz, false, prev_free);

  /* creating new block from free space left and insert to free list*/
  addr = bt_incr_addr(new_node, sz); //(new_node);
  bt_set_boundaries(addr, diff, true, false);

  addr = merge(addr);
  insert(addr);
  last = MAX(addr, last);

  return new_node;
}

/* returns null on failure  else find best suited of at least sz size*/
static inline word_t *find_best(word_t sz) {
  if (!free_list)
    return NULL;
  word_t *best;
  word_t *list_node = free_list;

  best = list_node;
  word_t diff = bt_size(best) - sz;
  word_t best_diff = diff;

  /* uncommenting break set to first-fit which is faster but has worse mem
   * utility*/
  while ((list_node = bt_next(list_node)) != free_list && best_diff != 0) {
    diff = bt_size(list_node) - sz;
    if (diff >= 0 && (diff < best_diff || best_diff < 0)) {
      best_diff = diff;
      best = list_node;
      // break;
    }
  }
  /* failed to found, malloc will have to call sbrk*/
  if (best_diff < 0)
    return NULL;

  list_remove(best);
  return get_block(best, sz);
}
/* --=[ mm_init ]=---------------------------------------------------------- */

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  heap_end = mem_heap_hi(); //(void *)heap_end + size;
  return ptr;
}

int mm_init(void) {
  /* allocate memory for initial empty head*/
  heap_start = mem_heap_lo();
  last = heap_start;
  void *ptr = morecore(ALIGNMENT - sizeof(word_t));
  if (ptr == (void *)-1)
    return -1;
  heap_end = mem_heap_hi();
  free_list = NULL;

  return 0;
}

/* ------------- Main functionality------------------------ */
static inline word_t *extend_heap(size_t size) {
  // extend heap by CHUNK, return to malloc block of asked size and put rest
  //  on the free list
  size_t alloc_size = MAX(CHUNKSIZE, size);
  word_t *bp = morecore(alloc_size);

  bt_set_boundaries(bp, alloc_size, true, false);
  bp = merge(bp);
  /*return used block of size, put rest on free list handle prev_free*/
  return get_block(bp, size);
}

/* make sure it's multiple of 16 bytes  or 4 words */
static size_t round_up(size_t size) {
  /*incr by 4 cause sizes we store includes header*/
  size += sizeof(word_t);
  size = (size + ALIGNMENT - 1) & -ALIGNMENT;
  return size;
}

void *malloc(size_t size) {
  if (size == 0)
    return NULL;

  /* make proper size*/
  size = round_up(size);

  word_t *address = find_best(size);
  if (!address) {
    address = extend_heap(size);
  }
  return bt_payload(address);
}

void free(void *ptr) {

  if (!ptr)
    return;

  word_t *block = bt_fromptr(ptr);
  bool prev_free = bt_get_prevfree(block);
  bt_set_boundaries(block, bt_size(block), true, prev_free);

  block = merge(block);
  insert(block);

  if (block < last)
    bt_set_prevfree(bt_physical_next(block));
}

/* realloc - Change the size of the block by mallocing a new block,
   copying its data, and freeing the old block. */
void *realloc(void *old_ptr, size_t sz) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (sz == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(sz);

  void *new_ptr = malloc(sz);
  /* If malloc() fails, the original block is left untouched. */

  if (!new_ptr)
    return NULL;

  /* Else Copy the old data */
  size_t old_size = bt_size(old_ptr);
  if (sz < old_size)
    old_size = sz;
  memcpy(new_ptr, old_ptr, old_size);
  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*  calloc - Allocate the block and set it to zero. */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

static inline bool on_list(word_t *e) {
  word_t *list_node = free_list;
  if (!e)
    return false;
  if (e == list_node)
    return true;
  while ((list_node = bt_next(list_node)) != free_list) {
    if (list_node == e)
      return true;
  }
  return false;
}
static inline bool on_heap(word_t *block) {
  return heap_start < block && block < heap_end;
}

/* check if:
   each element at free_list is set as free
   every elements set as free is on free_list
   there ane no two free blocks next to each other
   next and previous adderesses are addereses on heap
  pointers on list of free blocks point to beginings of free blocks*/
void mm_checkheap(int verbose) {
  word_t *start = heap_start;
  bool prev_free = false;
  while (start <= last) {
    bool on_the_list = on_list(start);
    if (bt_free(start) && !on_the_list)
      printf("Element is set as free but can't be found on free-list\n");
    if (bt_used(start) && on_the_list)
      printf("Element is on the free-list but it is set as used\n");
    if (!on_heap(bt_prev(start)))
      printf("Element set as previous is not on the heap\n");
    if (!on_heap(bt_next(start)))
      printf("Eement set as next is not on the heap\n");
    if (bt_free(start) && prev_free)
      printf("block should be coalesced with previous one\n");
    prev_free = bt_free(start);
    start = bt_physical_next(start);
  }
}