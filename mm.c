/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "YAM",
    /* First member's full name */
    "Cauim de Souza Lima",
    /* First member's email address */
    "cauim.de-souza-lima@polytechnique.edu",
    /* Second member's full name (leave blank if none) */
    "Ian Duleba",
    /* Second member's email address (leave blank if none) */
    "ian.duleba@polytechnique.edu"
};

/* Minimum block size */
#define MIN_BLK_SIZE 8

/* Single word size */
#define WSIZE 4

/* Double word size */
#define DSIZE 8

/* Returns the maximum/minimum of two integers */
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) > (y) ? (y) : (x))

/* Pack a size, previous_allocated bit and allocated bit into a word */
#define PACK(size, prev_alloc, alloc) ((size) | ((prev_alloc) << 1) | (alloc))

/* Read and write a word at adress p */
#define GET(p)		(*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)		(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)

/* Return 1 iff PINUSE_BIT field from address p is set */
#define GET_PALLOC(p) (!!(GET(p) & 0x2))

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *) (bp) - WSIZE)
#define FTRP(bp) ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


static char *heap_listp;


static void place(void *bp, size_t asize);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);

/* 
 * mm_init - creates a heap with an initial free block
 */
int mm_init(void)
{
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) return -1;
	PUT(heap_listp, 0);									/* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1, 1));	/* Prologue header */
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1, 1));		/* Epilogue header */
	heap_listp += DSIZE;

	if (extend_heap(mem_pagesize() / WSIZE) == NULL) return -1;

	printf("INTIALIZED WITH SIZE %d\n", GET_SIZE(HDRP(NEXT_BLKP(heap_listp))));
	printf("End of heap: %p\n\n", NEXT_BLKP(NEXT_BLKP(heap_listp)));

    return 0;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
#ifdef DEBUG
	printf("Calling malloc with size = %d\n", size);
#endif
	size_t asize;			/* Adjusted block size */
	size_t extendsize;		/* Amount to extend heap if no fit */
    char *bp;

	if (size == 0) return NULL;

	if (size <= DSIZE) asize = DSIZE;
	else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}

	extendsize = MAX(asize, mem_pagesize());
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;
	place(bp, asize);
#ifdef DEBUG
	printf("\tCreated new block at %p with %d bytes\n\n", bp, GET_SIZE(HDRP(bp)));
#endif
	return bp;
}

/*
 * mm_free - Updates header and footer and coalesce with neighbors
 */
void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	size_t prev_alloc = GET_PALLOC(HDRP(bp));
#ifdef DEBUG
	printf("Calling mm_free with bp = %p\n", bp);
	printf("\tblock size = %d bytes and PINUSE_BIT = %d\n", size, prev_alloc);
#endif

	PUT(HDRP(bp), PACK(size, prev_alloc, 0));
	PUT(FTRP(bp), PACK(size, prev_alloc, 0));

	char *next_bp = NEXT_BLKP(bp);
	size_t next_size = GET_SIZE(HDRP(next_bp));
	size_t next_alloc = GET_ALLOC(HDRP(next_bp));
	PUT(HDRP(next_bp), PACK(next_size, 0, next_alloc));

#ifdef DEBUG
	printf("\t%d bytes freed\n\n", GET_SIZE(HDRP(bp)));
#endif
	coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    copySize = MIN(size, GET_SIZE(HDRP(ptr)));
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}


/*
 * extend_heap - Extends the heap with a new free block
 */
static void *extend_heap(size_t words)
{
#ifdef DEBUG
	printf("Call to extend heap with words = %d\n", words);
#endif
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain aligment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((long) (bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footerand the epilogue header */
	size_t prev_alloc = GET_PALLOC(HDRP(bp));
	PUT(HDRP(bp), PACK(size, prev_alloc, 0));		/* Free block header */
	PUT(FTRP(bp), PACK(size, prev_alloc, 0));		/* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1));		/* New epilogue header */
#ifdef DEBUG
	printf("\tnew block created with %d bytes\n\n", size);
#endif

	/* Coalesce if the previous block was free */
	return coalesce(bp);
}


/*
 * coalesce - Coalesce block pointed by bp with its neighbors
 */
static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_PALLOC(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
#ifdef DEBUG
	printf("Called coalesce with bp = %p\n", bp);
	printf("\tPINUSE_BIT = %d, NINUSE = %d, size = %d\n\n", prev_alloc, next_alloc, size);
#endif

	if (prev_alloc && next_alloc) {
		/* Do nothing */
	}
	
	else if (prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 1, 0));
		PUT(FTRP(bp), PACK(size, 1, 0));
	}
	
	else if (!prev_alloc && next_alloc) {
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		/* The block before 'previous' is always in use */
		PUT(FTRP(bp), PACK(size, 1, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	}
	
	else {
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	}

	return bp;
}




/*
 * find_fit - Returns first free block with enough capacity
 */
static void *find_fit(size_t asize)
{
#ifdef DEBUG
	printf("Called find_fit with asize = %d\n", asize);
	int cunt = 1;
#endif
	char *bp;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (GET_SIZE(HDRP(bp)) >= asize && !GET_ALLOC(HDRP(bp))) {
#ifdef DEBUG
			printf("\tfound free block with %d bytes in the %d iteration at address %p\n\n"\
					, GET_SIZE(HDRP(bp)), cunt, bp);
#endif
			return bp;
		}
#ifdef DEBUG
		cunt++;
#endif
	}
#ifdef DEBUG
			printf("\tdidn't find any free block\n\n");
#endif
	return NULL;
}



/*
 * place - Place a new block of size at least asize in block
 * pointed by bp
 */
static void place(void *bp, size_t asize)
{
	size_t size = GET_SIZE(HDRP(bp));
	size_t prev_alloc = GET_PALLOC(HDRP(bp));
#ifdef DEBUG
	printf("Calling place with bp = %p and asize = %d\n", bp, asize);
	printf("\tcurrent block has size = %d bytes and PINSUSE_BIT = %d\n", size, prev_alloc);
#endif

	if (size >= asize + MIN_BLK_SIZE) {
		PUT(HDRP(bp), PACK(asize, prev_alloc, 1));

		char *next_bp = NEXT_BLKP(bp);
		PUT(HDRP(next_bp), PACK(size - asize, 1, 0));
		PUT(FTRP(next_bp), PACK(size - asize, 1, 0));
#ifdef DEBUG
	printf("\tfirst block with %d bytes, second block with %d bytes\n", \
			GET_SIZE(HDRP(bp)), GET_SIZE(HDRP(next_bp)));
	printf("\tsecond at adress %p, PINUSE_BIT = %d\n\n", next_bp, GET_PALLOC(HDRP(next_bp)));
#endif
	}

	else {
		PUT(HDRP(bp), PACK(size, prev_alloc, 1));

		char *next_bp = NEXT_BLKP(bp);
		size_t next_size = GET_SIZE(HDRP(next_bp));
		size_t next_alloc = GET_ALLOC(HDRP(next_bp));
		PUT(HDRP(next_bp), PACK(next_size, 1, next_alloc));
#ifdef DEBUG
	printf("\tonly one block with %d bytes\n\n", GET_SIZE(HDRP(bp)));
#endif
	}
}


