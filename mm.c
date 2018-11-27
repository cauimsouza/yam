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

/* Minimum allowed block size for allocation */
#define MIN_BLK_SIZE 24

/* Minimum block size for blocks in the mixed-size size class lists */
#define MIN_BIGBLK_SIZE 40

/* Single word size */
#define WSIZE 4

/* Double word size */
#define DSIZE 8

/* 
 * Define the maximum size class whose free blocks have
 * all the same size
 */
#define MAX_SINGLE_CLASS 2048

/* Number of size classes containing only one size */
#define NUM_SINGLE_SIZECLASSES (1 + (MAX_SINGLE_CLASS - MIN_BLK_SIZE) / DSIZE)

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
#define GET_PALLOC(p) 	(!!(GET(p) & 0x2))

/* Return 1 iff ROOT_BIT field from address p is set */
#define GET_ROOT(p)		(!!(GET(p) & 0x4))

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *) (bp) - WSIZE)
#define FTRP(bp) ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of next and previous free blocks
 * in the same size class */
#define NEXT_LISTP(bp) (*((void **)(bp)))
#define PREV_LISTP(bp) (*((void **)(bp) + 1))

/* Set pointers to next and previous list elements */
#define SET_NEXT_LISTP(bp, addr) (*((void **)(bp)) = (void *)(addr))
#define SET_PREV_LISTP(bp, addr) (*((void **)(bp) + 1) = (void *)(addr))

/* Given block ptr bp, compute address of next and previous size class 
 * free lists */
#define NEXT_CLASSP(bp) (*((void **)(bp) + 2))
#define PREV_CLASSP(bp) (*((void **)(bp) + 3))

/* Set pointers to next and previous size class tree lists */
#define SET_NEXT_CLASSP(bp, addr) (*((void **)(bp) + 2) = (void *)(addr))
#define SET_PREV_CLASSP(bp, addr) (*((void **)(bp) + 3) = (void *)(addr))

/* Set/unset ROOT_BIT of block pointed by bp to val */
#define SET_ROOT(bp)	(*((char *)(bp) - WSIZE) |= 0x4)
#define UNSET_ROOT(bp)	(*((char *)(bp) - WSIZE) &= ~0x4)

static void **heap_listp;
static char *prologuep;
static char *epiloguep;

static void place(void *bp, size_t asize);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static size_t get_sizeclass_size(size_t size);
static void insert_into_sizeclass(void *bp, void *cp);
static void create_sizeclass(void *bp, void *prev_cp, void *next_cp);
static size_t hibit(size_t x);
static void remove_from_sizeclass(void *bp);
static void insert_into_list(void *bp);
static void *init_array();
static size_t get_bin_id(size_t size);

static void traverse_lists();
static void traverse_blocks();

static void mm_check();


/* 
 * @brief Creates a heap with an initial free block.
 *
 * @return nothing
 */
int mm_init()
{
	char *bp;
	if( (bp = init_array()) == (void *)-1)
		return -1;

	if ((prologuep = mem_sbrk(2 * MIN_BIGBLK_SIZE + 8)) == (void *)-1)
		return -1;

	prologuep += DSIZE;
	epiloguep = prologuep + MIN_BIGBLK_SIZE;

	PUT(HDRP(prologuep), PACK(MIN_BIGBLK_SIZE, 1, 1));	/* Prologue header */
	SET_ROOT(prologuep);
	SET_PREV_LISTP(prologuep, prologuep);
	SET_NEXT_LISTP(prologuep, prologuep);
	SET_NEXT_CLASSP(prologuep, epiloguep);
	SET_PREV_CLASSP(prologuep, prologuep);

	PUT(HDRP(epiloguep), PACK(0, 1, 1));		/* Epilogue header */
	SET_ROOT(epiloguep);
	SET_PREV_LISTP(epiloguep, epiloguep);
	SET_NEXT_LISTP(epiloguep, epiloguep);
	SET_NEXT_CLASSP(epiloguep, epiloguep);
	SET_PREV_CLASSP(epiloguep, prologuep);


	if (extend_heap(mem_pagesize() / WSIZE) == NULL)
		return -1;

#ifdef DEBUG
	printf("INTIALIZED WITH SIZE %d\n", GET_SIZE(HDRP(NEXT_BLKP(prologuep))));
	printf("End of heap: %p\n\n", NEXT_BLKP(NEXT_BLKP(prologuep)));

	traverse_lists();
	traverse_blocks();
	mm_check();
#endif

    return 0;
}

/* 
 * @brief Allocates a block by incrementing the brk pointer.
 * 
 * Always allocate a block whose size is a multiple of the alignment.
 *
 * @param size size
 * @return pointer to a new allocated block whose size is at least
 * size.
 */
void *mm_malloc(size_t size)
{
#ifdef DEBUG
	printf("Calling malloc with size = %d\n", size);
#endif
	size_t asize;			/* Adjusted block size */
	size_t extendsize;		/* Amount to extend heap if no fit */
    char *bp;

	if (size == 0)
		return NULL;

	if (size <= MIN_BIGBLK_SIZE)
		asize = MIN_BIGBLK_SIZE;
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
    	remove_from_sizeclass(bp);
		place(bp, asize);
#ifdef DEBUG
		printf("\tCreated new block at %p with %d bytes\n\n", bp, GET_SIZE(HDRP(bp)));
		traverse_lists();
		traverse_blocks();
		mm_check();
#endif
		return bp;
	}

	extendsize = MAX(asize, mem_pagesize());
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return NULL;
	remove_from_sizeclass(bp);
	place(bp, asize);
#ifdef DEBUG
	printf("\tCreated new block at %p with %d bytes\n\n", bp, GET_SIZE(HDRP(bp)));
	traverse_lists();
	traverse_blocks();
#endif
	return bp;
}

/*
 * @brief Frees an allocated block.
 *
 * @param pointer to allocated block
 * @return nothing
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
	bp = coalesce(bp);
	insert_into_list(bp);

#ifdef DEBUG
	traverse_lists();
	traverse_blocks();
	mm_check();
#endif
}

/*
 * @brief Reallocates an allocated block and copies
 * its data.
 *
 * Copies the first size bytes of the old allocated
 * block into the new block if the new block has a
 * capacity at least equal to size. If its capacity
 * is smaller than size, then a number of bytes igual
 * to its capacity is copied.
 *
 * @param ptr pointed to allocated block
 * @param size size of the new allocated block
 * @return pointer to the new allocated block
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
    	return NULL;

    copySize = MIN(size, GET_SIZE(HDRP(ptr)));
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * @brief Extends the heap with a new free block.
 *
 * @param words number of words units by which the heap
 * will increase (rounded up to nearest pair integer)
 * @return pointer to the last free block in the heap
 * after the extension.
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

	bp = epiloguep;
	epiloguep += size;

	/* Initialize free block header/footerand the epilogue header */
	size_t prev_alloc = GET_PALLOC(HDRP(bp));
	PUT(HDRP(bp), PACK(size, prev_alloc, 0));		/* Free block header */
	PUT(FTRP(bp), PACK(size, prev_alloc, 0));		/* Free block footer */

	PUT(HDRP(epiloguep), PACK(0, 0, 1));		/* New epilogue header */
	SET_ROOT(epiloguep);
	SET_PREV_CLASSP(epiloguep, PREV_CLASSP(bp));
	SET_NEXT_CLASSP(epiloguep, epiloguep);
	SET_NEXT_LISTP(epiloguep, epiloguep);
	SET_PREV_LISTP(epiloguep, epiloguep);

	SET_NEXT_CLASSP(PREV_CLASSP(bp), epiloguep);
#ifdef DEBUG
	printf("\tnew block created with %d bytes, palloc = %d\n\n", size, prev_alloc);
#endif

	/* Coalesce if the previous block was free */
	bp = coalesce(bp);
	insert_into_list(bp);

	return bp;
}

/*
 * @brief Coalesce free block with its neighbors.
 *
 * @param bp pointer to free block. This free block
 * should not be in the lists data structure.
 * @return pointer to coalesced free block
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
#ifdef DEBUG
		printf("\t1 case\n");
#endif
	} else if (prev_alloc && !next_alloc) {
#ifdef DEBUG
		printf("\t2 case\n");
#endif
		remove_from_sizeclass(NEXT_BLKP(bp));

		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 1, 0));
		PUT(FTRP(bp), PACK(size, 1, 0));
	} else if (!prev_alloc && next_alloc) {
#ifdef DEBUG
		printf("\t3 case: previous %p size %d\n", PREV_BLKP(bp), GET_SIZE(HDRP(PREV_BLKP(bp))));
#endif
		remove_from_sizeclass(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		/* The block before 'previous' is always in use */
		PUT(FTRP(bp), PACK(size, 1, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	} else {
#ifdef DEBUG
		printf("\t4 case\n");
#endif
		remove_from_sizeclass(NEXT_BLKP(bp));
		remove_from_sizeclass(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	}

	return bp;
}

/*
 * @brief Returns first free block with enough size,
 * or NULL if such a free block does not exist.
 *
 * @param asize minimum size of block to be allocated
 * @return pointer to free block whose size is at least
 * asize
 */
static void *find_fit(size_t asize)
{
	/*
	 * if asize corresponds to a size of fixed-size
	 * size class, then we try to allocate from its
	 * corresponding fixed-size list
	 */
	if (asize <= MAX_SINGLE_CLASS) {
		int bin_id = get_bin_id(asize);

		int i;
		for (i = bin_id; i < NUM_SINGLE_SIZECLASSES; i++) {
			void **list_p = heap_listp + i;

			if (*list_p != NULL) 
				return *list_p;
		}
	}

	/*
	 * if asize is greater than or equal to MAX_SINGLE_CLASS,
	 * then we look in the list of mixed-sized size classes
	 */
	char *cp;
	for (cp = NEXT_CLASSP(prologuep); GET_SIZE(HDRP(cp)) > 0; cp = NEXT_CLASSP(cp)) {
		size_t sizeclass_size = get_sizeclass_size(GET_SIZE(HDRP(cp)));

		if (sizeclass_size >= asize) {
			char *bp = cp;

			/* iterate over the double-linked list trying to find
			 * a free block that is large enough
			 */
			do {
				if (GET_SIZE(HDRP(bp)) >= asize)
					return bp;
				bp = NEXT_LISTP(bp);
			} while (bp != cp);
		}
	}

	return NULL;
}

/*
 * @brief Places a new block of size at least asize in free block
 * pointed by bp.
 *
 * @param bp pointer to free block
 * @param asize minimum size of block to be allocated
 * @return nothing
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
		insert_into_list(next_bp);
	} else {
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

/*
 * @brief Returns the maximum size of a free block that can
 * be contained in the free list containing a block
 * of size 'size'
 *
 * @param size size
 * @return maximum possible size of a free block in the
 * size class containing this size
 */
static size_t get_sizeclass_size(size_t size)
{
	if (size <= MAX_SINGLE_CLASS)
		return size;
	size_t msb = hibit(size);
	return msb << (msb == size ? 0 : 1);
}

/*
 * @brief Remove free block bp from its size class double-linked
 * list.
 *
 * @param bp pointer to free block to be removed from its size
 * class
 * @return nothing
 */
static void remove_from_sizeclass(void *bp)
{
	size_t block_size = GET_SIZE(HDRP(bp));
	size_t block_sizeclass_size = get_sizeclass_size(block_size);

	/*
	 * case where block is contained in a fixed-size
	 * size class list
	 */
	if (block_sizeclass_size <= MAX_SINGLE_CLASS) {
		int bin_id = get_bin_id(block_sizeclass_size);
		void **list_p = heap_listp + bin_id;
		void *prev_list_ptr = PREV_LISTP(bp),
			 *next_list_ptr = NEXT_LISTP(bp);

		if (prev_list_ptr != NULL)
			SET_NEXT_LISTP(prev_list_ptr, next_list_ptr);
		if (next_list_ptr != NULL)
			SET_PREV_LISTP(next_list_ptr, prev_list_ptr);
		if (*list_p == bp)
			*list_p = next_list_ptr;
		return;
	}

	char *prev_class_ptr = PREV_CLASSP(bp),
		 *next_class_ptr = NEXT_CLASSP(bp),
		 *prev_list_ptr = PREV_LISTP(bp),
		 *next_list_ptr = NEXT_LISTP(bp);

#ifdef DEBUG
	printf("Called remove from sizeclass with bp = %p, size = %d\n", bp, GET_SIZE(HDRP(bp)));
#endif

	/*
	 * bp is the only block in its free list,
	 * so we remove its list
	 */
	if (prev_list_ptr == bp) {
		SET_NEXT_CLASSP(prev_class_ptr, next_class_ptr);
		SET_PREV_CLASSP(next_class_ptr, prev_class_ptr);
		return;
	}

	SET_NEXT_LISTP(prev_list_ptr, next_list_ptr);
	SET_PREV_LISTP(next_list_ptr, prev_list_ptr);

	/*
	 * bp is the root of its list, the next
	 * free block in its list becomes the root
	 */
	if (GET_ROOT(HDRP(bp))) {
		SET_ROOT(HDRP(next_list_ptr));
		SET_PREV_CLASSP(next_list_ptr, prev_class_ptr);
		SET_NEXT_CLASSP(next_list_ptr, next_class_ptr);

		SET_NEXT_CLASSP(prev_class_ptr, next_list_ptr);
		SET_PREV_CLASSP(next_class_ptr, next_list_ptr);
	}
}

/*
 * @brief Inserts a free block into the size classes'
 * data structure.
 *
 * @param bp pointer to free block
 * @return nothing
 */
static void insert_into_list(void *bp)
{
#ifdef DEBUG
	printf("Called insert_into_list with bp = %p, size = %d\n", bp, GET_SIZE(HDRP(bp)));
#endif

	size_t block_size = GET_SIZE(HDRP(bp));
	size_t block_sizeclass_size = get_sizeclass_size(block_size);

	/*
	 * if possible, insert the free block in one fixed-size
	 * size class list
	 */
	if (block_sizeclass_size <= MAX_SINGLE_CLASS) {
		int bin_id = get_bin_id(block_sizeclass_size);
		void **list_p = heap_listp + bin_id;

		if (*list_p != NULL) 
			SET_PREV_LISTP(*list_p, bp);

		SET_NEXT_LISTP(bp, *list_p);
		SET_PREV_LISTP(bp, NULL);
		*list_p = bp;
		return;
	}

	char *cp;
	for (cp = NEXT_CLASSP(prologuep); GET_SIZE(HDRP(cp)) > 0; cp = NEXT_CLASSP(cp)) {
		size_t sizeclass_size = get_sizeclass_size(GET_SIZE(HDRP(cp)));

		if (block_sizeclass_size == sizeclass_size) {
			insert_into_sizeclass(bp, cp);
			return;
		} else if (block_sizeclass_size < sizeclass_size) {
		 	 create_sizeclass(bp, PREV_CLASSP(cp), cp);
		 	 return;
		 }
	}

	create_sizeclass(bp, PREV_CLASSP(cp), cp);
}

/*
 * @brief Inserts a new free block into the double-linked
 * list of its size class.
 *
 * @param bp pointer to the free block
 * @param cp pointer to size class' root block
 * @return nothing
 */
static void insert_into_sizeclass(void *bp, void *cp)
{
#ifdef DEBUG
	printf("bp = %p, size = %d\n", bp, GET_SIZE(HDRP(bp)));
	printf("cp = %p, size = %d\n", cp, GET_SIZE(HDRP(cp)));
#endif
	char *next_bp = NEXT_LISTP(cp);
	SET_NEXT_LISTP(bp, next_bp);
	SET_PREV_LISTP(bp, cp);
	SET_PREV_LISTP(next_bp, bp);
	SET_NEXT_LISTP(cp, bp);
	UNSET_ROOT(bp);

	assert(PREV_LISTP(bp) == cp);
	assert(NEXT_LISTP(bp) == cp);
}

/*
 * @brief Creates a new sizeclass double-linked list
 * containing only the block pointed by bp.
 *
 * @param bp pointer to the free block
 * @param prev_cp pointer to root of previous sizeclass' double-linked list
 * @param next_cp pointer to root of next sizeclass' double-linked list
 * @return nothing
 */
static void create_sizeclass(void *bp, void *prev_cp, void *next_cp)
{
	SET_NEXT_LISTP(bp, bp);
	SET_PREV_LISTP(bp, bp);
	SET_PREV_CLASSP(bp, prev_cp);
	SET_NEXT_CLASSP(bp, next_cp);
	SET_NEXT_CLASSP(prev_cp, bp);
	SET_PREV_CLASSP(next_cp, bp);
	SET_ROOT(bp);
}

/* @brief Returns the greatest power of 2 lower than x.
 *
 * @param x positive integer
 * @return greatest power of 2 lower than x
 */
static size_t hibit(size_t x)
{
	x |= (x >> 1);
	x |= (x >> 2);
	x |= (x >> 4);
	x |= (x >> 8);
	x |= (x >> 16);
	return x ^ (x >> 1);
}

/*
 * @brief Initalizes the array of pointers to the
 * fixed-size size class lists.
 *
 * @return pointer to the first element in the array
 */
static void *init_array()
{
	if((heap_listp = mem_sbrk(DSIZE * NUM_SINGLE_SIZECLASSES)) == (void *) -1)
		return (void *)-1;

	void **cp = heap_listp;
	int i;
	for (i = 0; i < NUM_SINGLE_SIZECLASSES; i++) {
		*cp = 0;	
		cp++;
	}

	return heap_listp;
}

/*
 * @brief Returns the bin id for the size class
 * of given size.
 *
 * @param size size of the fixed size class (should
 * be a multiple of 8 and greater or equal to MIN_BLK_SIZE)
 * @return bin id of the corresponding size class.
 */
static size_t get_bin_id(size_t size)
{
	return (size - MIN_BLK_SIZE) / DSIZE;
}

static void traverse_lists()
{
	char *cp = prologuep;
	while (1) {
		int size = GET_SIZE(HDRP(cp));
		printf("This size is %d\n", size);
		size_t sizeclass_size = get_sizeclass_size(size);
		printf("New class [%d, %d]\n", (sizeclass_size >> 1) + 1, sizeclass_size);

		char *cur_bp = cp;
		do {
			printf("\t%d\n", GET_SIZE(HDRP(cur_bp)));
			cur_bp = NEXT_LISTP(cur_bp);
		} while (cur_bp != cp);
		printf("end of list\n\n");

		if (GET_SIZE(HDRP(cp)) == 0)
			return;
		cp = NEXT_CLASSP(cp);
	}
}

static void traverse_blocks()
{
	printf("Traversing blocks\n");
	char *cp = prologuep;
	while (1) {
		int size = GET_SIZE(HDRP(cp));
		int alloc = GET_ALLOC(HDRP(cp));
		int palloc = GET_PALLOC(HDRP(cp));
		printf("\tsize = %d, alloc = %d, palloc = %d\n", size, alloc, palloc);

		if (size == 0)
			return;

		cp = NEXT_BLKP(cp);
	} 
}

/*
 * Framework for testing
 */

#define FAIL() printf("\nfailure in %s() line %d\n", __func__, __LINE__)
#define _assert(test) do { if (!(test)) { FAIL(); return 0; } } while (0)
#define _verify(test) do { int r = test(); tests_run++; if (!r) return r; } while (0)
static int tests_run = 0;


/*
 * Unit tests
 */

/*
 * @brief Runs all tests.
 *
 * @return 1 if all the tests passed,
 * 0 otherwise
 */
static int all_tests()
{
	tests_run = 0;

	return 1;
}

/*
 * @brief Performs consistency tests and terminates
 * the program if any of them fails.
 *
 * @return nothing
 */
static void mm_check()
{
	if (all_tests())
		printf("All tests passed. Tests run: %d\n", tests_run);
	else
		exit(0);
}
