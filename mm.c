
/*
 * mm.c
 * ID: hanw3
 * Name: Han Wang
 * Overview of my code:

 In my malloc optimazation, I used segeragated list to store 
 the free blocks. I split the free block lists into 19 different
 lists. Each list should contain free blocks with certain size.Particularly,
 I spilt my segragated lists as [[32,64),[64,128), [128,256),
 [256,512)...[2^n,2^(n+1))...[2^23,infinity)]. As for the block data structure,
 I used two pointer prev and next to indicate in the free segragated list, where
 is the block's prev and next block.But for allocated block, these two pointers
 are not exsisted. So I used union to store the payload(use when allocated) and these
 two pointers(use when free).

In addition, I stored three global variables: blockpointer, begin[], end[].
The blockpointer is a pointer point to current heap's last block(not incldude Prologue footer
and Epilogue header). The begin and end list used to store the first block and last block in
each of the 19 segeragated lists I mentioned above. So the begin and end length are the same as
the number of segragated lists--19. 

As for the strategy of malloc, each time a new free block needs to be added in the corresponding
free list, I search for the correct list based on the size of the block and store it at the end
of the list.Each time when I want to take a free block out and allocate it, I search for the 
corresponding free list based on the size of the allocated size and from the beginning of the
list and return the right one, if I cannot find one in current list, I search for the consecutive
next free list which store bigger blocks. So my strategy is first fit and FIFO(first in first out).

And as for the coalescing strategy, I used 




 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want debugging output, uncomment the following.  Be sure not
 * to have debugging enabled in your final submission
 */
 //#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__) 
#define dbg_checkheap(...) mm_checkheap(__VA_ARGS__)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#define dbg_requires(...)
#define dbg_ensures(...)
#define dbg_checkheap(...)
#define dbg_printheap(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    union{

    char payload[0];
    struct{
        struct block *prev;
        struct block *next;
          };
    };

} block_t;

/* Global variables */
/* Pointer to first block */
static block_t *heap_listp = NULL;
// static block_t *begin = NULL;
// static block_t *end = NULL;
static block_t *blockpointer = NULL;
//initialize list of begin and end for segragated list
static block_t *begin[19];
static block_t *end[19];

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prev_alloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool prev_alloc, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);
static void remove_free_list(block_t* block);
static void add_free_list(block_t* block);
bool mm_checkheap(int lineno);
static int blockindex(size_t size);
static bool get_prev_alloc(block_t *block);
static bool extract_prev_alloc(word_t word);
/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x) {
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*
 * Initialize: return false on error, true on success.
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1) 
    {
        return false;
    }
    // initialize the segragated list
    int i;
    for(i = 0; i<19; ++i){

        begin[i] = NULL;
        end[i] = NULL;
    }

    start[0] = pack(0, true, true); // Prologue footer
    start[1] = pack(0, true, true); // Epilogue header
    // Heap starts with first block header (epilogue)
    heap_listp = (block_t *) &(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

void *malloc(size_t size) 
{
    dbg_requires(mm_checkheap);
   
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_listp == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap);
        return bp;
    }
   dbg_printf("initial asked size is %lu! \n",(word_t)size);
    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size+wsize, dsize);
    asize = max(asize, min_block_size);
    dbg_printf("processed asize is %lu! \n",(word_t)asize);
    // Search the free list for a fit
    block = find_fit(asize);
   // dbg_printf("Entering Malloc phase correctly\n");
    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        dbg_printf("fit error! \n");
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            dbg_printf("extend error! \n");
            return bp;
        }

    }
   dbg_printf("ready to go to place! \n");
    place(block, asize);
    bp = header_to_payload(block);

     dbg_printf("Malloc size %zd on address %lu.\n", asize, (word_t)block);
    dbg_ensures(mm_checkheap);
  //  mm_checkheap(__LINE__);
    return bp;
} 

/*
 * free
 */

void free(void *ptr)
{
    if (ptr == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(ptr);
    size_t size = get_size(block);

    bool boolprev = get_prev_alloc(block);
    write_header(block, size, boolprev,false);
    write_footer(block, size, false);
    dbg_printf("Free size %zd on address %lu.\n", size,(word_t)block);
         coalesce(block);
       // mm_checkheap(__LINE__);


}

/*
 * realloc
 */

void *realloc(void *oldptr, size_t size)
{
    block_t *block = payload_to_header(oldptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(oldptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (oldptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, oldptr, copysize);

    // Free the old block
    free(oldptr);

    return newptr;
}
/*
 * calloc
 * This function is not tested by mdriver
 */
void *calloc(size_t nmemb, size_t size)
{
    void *bp;
    size_t asize = nmemb * size;

    if (asize/nmemb != size)
    // Multiplication overflowed
    return NULL;
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}


/*
 * extend_heap: Extends the heap with the requested number of bytes, and
 *              recreates epilogue header. Returns a pointer to the result of
 *              coalescing the newly-created block with previous free block, if
 *              applicable, or NULL in failure.
 */
static block_t *extend_heap(size_t size) 
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);

    if (blockpointer== NULL){

    write_header(block, size,true,false);
     blockpointer = block;
    }

    else{
        bool boolprev = get_alloc(blockpointer);
        write_header(block, size,boolprev,false);
        blockpointer = block;

    }
    
    write_footer(block, size, false);
   

    
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, false, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* Coalesce: Coalesces current block with previous and next blocks if either
 *           or both are unallocated; otherwise the block is not modified.
 *           Returns pointer to the coalesced block. After coalescing, the
 *           immediate contiguous previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t * block) 
{
    block_t *block_next = find_next(block);
   

    bool prev_alloc = get_prev_alloc(block);
    bool next_alloc = get_alloc(block_next);
    size_t size = get_size(block);
    size_t next_size = get_size(block_next);

    if (prev_alloc && next_alloc)              // Case 1
    {

        add_free_list(block);// add the middle free block to free list
        if(blockpointer != block)
        {

        write_header(block_next, next_size,false,true);

        }
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {
        
        size += get_size(block_next);
        //first remove the next free block in the free list
        remove_free_list(block_next);
        if (block_next == blockpointer)
        {
            blockpointer = block;
        }
        write_header(block, size, true,false);
        write_footer(block, size, false);
        // then add the new combined free block to the free list
        add_free_list(block);
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
        block_t *block_prev = find_prev(block);
        size += get_size(block_prev);
        
        //first remove the next free block in the free list
        remove_free_list(block_prev);
        if (block == blockpointer)
        {
            blockpointer = block_prev;
        }
        write_header(block_prev, size, true,false);
        write_footer(block_prev, size, false);

        if(block != blockpointer){
        write_header(block_next, next_size, false,true);
    }
        block = block_prev;
        //then add the new combined free block to the free list
        add_free_list(block);
    }

    else                                     // Case 4
    {
        block_t *block_prev = find_prev(block);
        size += get_size(block_next) + get_size(block_prev);
        // first remove both the former and latter free block in the free
        // list
        remove_free_list(block_next);
        remove_free_list(block_prev);
        if(block_next == blockpointer)
        {
        blockpointer = block_prev;
        }
        write_header(block_prev, size, true,false);
        write_footer(block_prev, size, false);

        block = block_prev;
        // add the noew combined free block into the free list
        add_free_list(block);
    }
    return block;
}

/*
 * place: Places block with size of asize at the start of bp. If the remaining
 *        size is at least the minimum block size, then split the block to the
 *        the allocated block and the remaining block as free, which is then
 *        inserted into the segregated list. Requires that the block is
 *        initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    dbg_printf("Entering place correctly with %lu to place\n", (word_t) asize);
    dbg_printf("Entering place correctly with block %lu \n", (word_t) block);
    size_t csize = get_size(block);
     dbg_printf("csize is %lu \n", (word_t) csize);
     dbg_printf("min size is %lu \n", (word_t) min_block_size);
    // remove the free block which is being used
    remove_free_list(block);

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        bool boolprev = get_prev_alloc(block);
        write_header(block, asize, boolprev,true);
        //write_footer(block, asize, true);
        block_next = find_next(block);
        if(block == blockpointer)
        {
            blockpointer = block_next;
        }
        
        write_header(block_next, csize-asize, true,false);
        write_footer(block_next, csize-asize, false);
        // add the free block which is the newly created
        add_free_list(block_next);
    }

    else
    { 
         bool boolprev = get_prev_alloc(block);
        write_header(block, csize, boolprev,true);
       // write_footer(block, csize, true);
     
       if(block!= blockpointer)
       {
        block_t *block_next = find_next(block);
        size_t next_size = get_size(block_next);
        bool boolnext = get_alloc(block_next);
         write_header(block_next, next_size,true,boolnext);
       }

    }
}

/*
 * find_fit: in the free list, looks for the fit size block to return
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;
    int i;

for(i = blockindex(asize); i<=18; ++i){

    if (begin[i]==NULL)
    {
        continue;
    }

    block = begin[i];
    
    while (block!= NULL)
    {
       //  mm_checkheap(__LINE__);
        if (asize <= get_size(block))
        {
            dbg_printf("Entering find_fit phase correctly\n");
            return block;
        }
        block = block->next;
        if (block == end[i])
            break;
    }
    
}

return NULL; 
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool prev_alloc, bool alloc)
{

     if (alloc && prev_alloc)
    {
        return (size | 3);
     
    }
    else if (!alloc && prev_alloc)
    {
       return (size | 2);
    }
    else if (alloc && !prev_alloc)
    {
       return (size | 1);
    }
    else{

       return size;

    }
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    dbg_printf("the header is: %lu\n", block->header);
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool prev_alloc, bool alloc)
{
    block->header = pack(size, prev_alloc, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    bool boolprev = get_prev_alloc(block);
    *footerp = pack(size, boolprev, alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}
/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}

/* mm_checkheap: checks the heap for correctness; returns true if
 *               the heap is correct, and false otherwise.
 *               can call this function using mm_checkheap(__LINE__);
 *               to identify the line number of the call site.
 */
bool mm_checkheap(int lineno)  
{ 

    printf("free list condition as follw:\n");
    for(int i=0; i<19;++i)
    {
        block_t *tmp = begin[i];
        printf("free list No.%d begin pointer is : %lu\n", i,(word_t)tmp);
    }

    printf("the blockpointer is %lu \n", (word_t)blockpointer);
    printf("the current heap structure is: \n");
     block_t *blocknode = heap_listp;
    while(get_size(blocknode))
    {
        word_t *footer = (word_t *)((blocknode->payload) + get_size(blocknode) - dsize);
        printf("header:%lu, allocate condition: %d,prev allocated condition: %d, size:%lu, footer:%lu, block:%lu-->",
            (word_t)blocknode->header, (int)get_alloc(blocknode),(int) get_prev_alloc(blocknode),(word_t)get_size(blocknode), (word_t)footer, (word_t)blocknode);
        blocknode = find_next(blocknode);
    }
    printf("\n");
    printf("this is the end of the heap.\n");
    return true;

}

static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);
}

static bool extract_prev_alloc(word_t word)
{
    return (bool)(word & prev_alloc_mask);
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}
/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p) {
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

static void add_free_list(block_t* block) {

    int i = blockindex(get_size(block));

if (begin[i]==NULL && end[i] == NULL)
    {
     block->prev = NULL;
     block->next = NULL;
     begin[i] = block;
     end[i] = block;
    }


else if(begin[i] && end[i])
    {
     
     block->prev = end[i];
     end[i]->next = block;

     block->next = NULL;
     end[i] = block;

    }

}

static void remove_free_list(block_t* block) {

    int i = blockindex(get_size(block));

if (begin[i] == block && end[i] == block)
    {
     begin[i] = NULL;
     end[i] = NULL;

    }
else if (begin[i] == block)
    {
    begin[i] = block->next;
    begin[i]->prev = NULL;
    }

else if (end[i] == block)
    {
    end[i] = block->prev;
    end[i]->next = NULL;
    }

else
    {
     block->prev->next = block->next;
     block->next->prev = block->prev;
    }

}

static int blockindex(size_t size){
    int i =0;
    unsigned int comp = 64;
    while(i<18 && comp < size){
        ++i;
        comp= comp<< 1;
    }
return i;
}