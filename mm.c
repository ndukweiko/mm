/*-------------------------------------------------------------------
 *  Malloc lab Starter code:
 *        single doubly-linked free block list with LIFO policy
 *        with support for coalescing adjacent free blocks
 *
 * Terminology:
 * o We will implement an explicit free list allocator
 * o We use "next" and "previous" to refer to blocks as ordered in
 *   the free list.
x * o We use "following" and "preceding" to refer to adjacent blocks
 *   in memory.
 *-------------------------------------------------------------------- */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "memlib.h"
#include "mm.h"

team_t team={
    "Teamn",                                        /* team name */
    "Ndukwe Iko",                                        /* first member full name */
    "nciko",                                        /* first member email address*/
    "",                                        /* second member full name -- don't remove */
    ""                                         /* second member email address  */
};
/* Macros for unscaled pointer arithmetic to keep other code cleaner.
   Casting to a char* has the effect that pointer arithmetic happens at
   the byte granularity (i.e. POINTER_ADD(0x1, 1) would be 0x2).  (By
   default, incrementing a pointer in C has the effect of incrementing
   it by the size of the type to which it points (e.g. BlockInfo).)
   We cast the result to void* to force you to cast back to the
   appropriate type and ensure you don't accidentally use the resulting
   pointer as a char* implicitly.  You are welcome to implement your
   own pointer arithmetic instead of using these macros.
*/
#define UNSCALED_POINTER_ADD(p,x) ((void*)((char*)(p) + (x)))
#define UNSCALED_POINTER_SUB(p,x) ((void*)((char*)(p) - (x)))


/******** FREE LIST IMPLEMENTATION ***********************************/


/* A BlockInfo contains information about a block, including the size
   and usage tags, as well as pointers to the next and previous blocks
   in the free list.  This is exactly the "explicit free list" structure
   illustrated in the lecture slides.

   Note that the next and prev pointers and the boundary tag are only
   needed when the block is free.  To achieve better utilization, mm_malloc
   should use the space for next and prev as part of the space it returns.

   +--------------+
   | sizeAndTags  |  <-  BlockInfo pointers in free list point here
   |  (header)    |
   +--------------+
   |     next     |  <-  Pointers returned by mm_malloc point here
   +--------------+
   |     prev     |
   +--------------+
   |  space and   |
   |   padding    |
   |     ...      |
   |     ...      |
   +--------------+
   | boundary tag |
   |  (footer)    |
   +--------------+
*/
struct BlockInfo {
  // Size of the block (in the high bits) and tags for whether the
  // block and its predecessor in memory are in use.  See the SIZE()
  // and TAG macros, below, for more details.
  size_t sizeAndTags;
  // Pointer to the next block in the free list.
  struct BlockInfo* next;
  // Pointer to the previous block in the free list.
  struct BlockInfo* prev;
};
typedef struct BlockInfo BlockInfo;


/* Pointer to the first BlockInfo in the free list, the list's head.

   A pointer to the head of the free list in this implementation is
   always stored in the first word in the heap.  mem_heap_lo() returns
   a pointer to the first word in the heap, so we cast the result of
   mem_heap_lo() to a BlockInfo** (a pointer to a pointer to
   BlockInfo) and dereference this to get a pointer to the first
   BlockInfo in the free list. */
#define FREE_LIST_HEAD *((BlockInfo **)mem_heap_lo())

/* Size of a word on this architecture. */
#define WORD_SIZE sizeof(void*)

/* Minimum block size (to account for size header, next ptr, prev ptr,
   and boundary tag) */
#define MIN_BLOCK_SIZE (sizeof(BlockInfo) + WORD_SIZE)

/* Alignment of blocks returned by mm_malloc. */
#define ALIGNMENT 8

/* SIZE(blockInfo->sizeAndTags) extracts the size of a 'sizeAndTags' field.
   Also, calling SIZE(size) selects just the higher bits of 'size' to ensure
   that 'size' is properly aligned.  We align 'size' so we can use the low
   bits of the sizeAndTags field to tag a block as free/used, etc, like this:

      sizeAndTags:
      +-------------------------------------------+
      | 63 | 62 | 61 | 60 |  . . . .  | 2 | 1 | 0 |
      +-------------------------------------------+
        ^                                       ^
      high bit                               low bit

   Since ALIGNMENT == 8, we reserve the low 3 bits of sizeAndTags for tag
   bits, and we use bits 3-63 to store the size.

   Bit 0 (2^0 == 1): TAG_USED
   Bit 1 (2^1 == 2): TAG_PRECEDING_USED
*/
#define SIZE(x) ((x) & ~(ALIGNMENT - 1))

/* TAG_USED is the bit mask used in sizeAndTags to mark a block as used. */
#define TAG_USED 1

/* TAG_PRECEDING_USED is the bit mask used in sizeAndTags to indicate
   that the block preceding it in memory is used. (used in turn for
   coalescing).  If the previous block is not used, we can learn the size
   of the previous block from its boundary tag */
#define TAG_PRECEDING_USED 2








/* Find a free block of the requested size in the free list.  Returns
   NULL if no free block is large enough. */
void examine_heap();


static void * searchFreeList(size_t reqSize) {
  BlockInfo* freeBlock;

  freeBlock = FREE_LIST_HEAD;
  while (freeBlock != NULL){
    if (SIZE(freeBlock->sizeAndTags) >= reqSize) {
      return freeBlock;
    } else {
      freeBlock = freeBlock->next;
    }
  }
  return NULL;
}


/* Insert freeBlock at the head of the list.  (LIFO) */
static void insertFreeBlock(BlockInfo* freeBlock) {
  BlockInfo* oldHead = FREE_LIST_HEAD;
  freeBlock->next = oldHead;
  if (oldHead != NULL) {
    oldHead->prev = freeBlock;
  }
  freeBlock->prev = NULL;
  FREE_LIST_HEAD = freeBlock;
}

/* Remove a free block from the free list. */
static void removeFreeBlock(BlockInfo* freeBlock) {
  BlockInfo *nextFree, *prevFree;

  nextFree = freeBlock->next;
  prevFree = freeBlock->prev;

  // If the next block is not null, patch its prev pointer.
  if (nextFree != NULL) {
    nextFree->prev = prevFree;
  }

  // If we're removing the head of the free list, set the head to be
  // the next block, otherwise patch the previous block's next pointer.
  if (freeBlock == FREE_LIST_HEAD) {
    FREE_LIST_HEAD = nextFree;
  } else {
    prevFree->next = nextFree;
  }
}

/* Coalesce 'oldBlock' with any preceeding or following free blocks. */
static void coalesceFreeBlock(BlockInfo* oldBlock) {
  BlockInfo *blockCursor;
  BlockInfo *newBlock;
  BlockInfo *freeBlock;
  // size of old block
  size_t oldSize = SIZE(oldBlock->sizeAndTags);
  // running sum to be size of final coalesced block
  size_t newSize = oldSize;

  // Coalesce with any preceding free block
  blockCursor = oldBlock;
  while ((blockCursor->sizeAndTags & TAG_PRECEDING_USED)==0) {
    // While the block preceding this one in memory (not the
    // prev. block in the free list) is free:

    // Get the size of the previous block from its boundary tag.
    size_t size = SIZE(*((size_t*)UNSCALED_POINTER_SUB(blockCursor, WORD_SIZE)));
    // Use this size to find the block info for that block.
    freeBlock = (BlockInfo*)UNSCALED_POINTER_SUB(blockCursor, size);
    // Remove that block from free list.
    removeFreeBlock(freeBlock);

    // Count that block's size and update the current block pointer.
    newSize += size;
    blockCursor = freeBlock;
  }
  newBlock = blockCursor;

  // Coalesce with any following free block.
  // Start with the block following this one in memory
  blockCursor = (BlockInfo*)UNSCALED_POINTER_ADD(oldBlock, oldSize);
  while ((blockCursor->sizeAndTags & TAG_USED)==0) {
    // While the block is free:

    size_t size = SIZE(blockCursor->sizeAndTags);
    // Remove it from the free list.
    removeFreeBlock(blockCursor);
    // Count its size and step to the following block.
    newSize += size;
    blockCursor = (BlockInfo*)UNSCALED_POINTER_ADD(blockCursor, size);
  }

  // If the block actually grew, remove the old entry from the free
  // list and add the new entry.
  if (newSize != oldSize) {
    // Remove the original block from the free list
    removeFreeBlock(oldBlock);


    // Save the new size in the block info and in the boundary tag
    // and tag it to show the preceding block is used (otherwise, it
    // would have become part of this one!).
    newBlock->sizeAndTags = newSize | TAG_PRECEDING_USED;
    // The boundary tag of the preceding block is the word immediately
    // preceding block in memory where we left off advancing blockCursor.
    *(size_t*)UNSCALED_POINTER_SUB(blockCursor, WORD_SIZE) = newSize | TAG_PRECEDING_USED;

    // Put the new block in the free list.
    insertFreeBlock(newBlock);
  }
  return;
}

/* Get more heap space of size at least reqSize. */
static void requestMoreSpace(size_t reqSize) {
  size_t pagesize = mem_pagesize();
  size_t numPages = (reqSize + pagesize - 1) / pagesize;
  BlockInfo *newBlock;
  size_t totalSize = numPages * pagesize;
  size_t prevLastWordMask;

  void* mem_sbrk_result = mem_sbrk(totalSize);
  if ((size_t)mem_sbrk_result == -1) {
    examine_heap();
    printf("ERROR: mem_sbrk failed in requestMoreSpace\n");
    exit(0);
  }
  newBlock = (BlockInfo*)UNSCALED_POINTER_SUB(mem_sbrk_result, WORD_SIZE);

  /* initialize header, inherit TAG_PRECEDING_USED status from the
     previously useless last word however, reset the fake TAG_USED
     bit */
  prevLastWordMask = newBlock->sizeAndTags & TAG_PRECEDING_USED;
  newBlock->sizeAndTags = totalSize | prevLastWordMask;
  // Initialize boundary tag.
  ((BlockInfo*)UNSCALED_POINTER_ADD(newBlock, totalSize - WORD_SIZE))->sizeAndTags =
    totalSize | prevLastWordMask;

  /* initialize "new" useless last word
     the previous block is free at this moment
     but this word is useless, so its use bit is set
     This trick lets us do the "normal" check even at the end of
     the heap and avoid a special check to see if the following
     block is the end of the heap... */
  *((size_t*)UNSCALED_POINTER_ADD(newBlock, totalSize)) = TAG_USED;

  // Add the new block to the free list and immediately coalesce newly
  // allocated memory space
  insertFreeBlock(newBlock);
  coalesceFreeBlock(newBlock);
}                                                                                                                   
    
 
/* Initialize the allocator. */
int mm_init () {
  // Head of the free list.
  BlockInfo *firstFreeBlock;

  // Initial heap size: WORD_SIZE byte heap-header (stores pointer to head
  // of free list), MIN_BLOCK_SIZE bytes of space, WORD_SIZE byte heap-footer.
  size_t initSize = WORD_SIZE+MIN_BLOCK_SIZE+WORD_SIZE;
  size_t totalSize;

  void* mem_sbrk_result = mem_sbrk(initSize);
  //  printf("mem_sbrk returned %p\n", mem_sbrk_result);
  if ((ssize_t)mem_sbrk_result == -1) {
    printf("ERROR: mem_sbrk failed in mm_init, returning %p\n",
           mem_sbrk_result);
    exit(1);
  }

  firstFreeBlock = (BlockInfo*)UNSCALED_POINTER_ADD(mem_heap_lo(), WORD_SIZE);

  // Total usable size is full size minus heap-header and heap-footer words
  // NOTE: These are different than the "header" and "footer" of a block!
  // The heap-header is a pointer to the first free block in the free list.
  // The heap-footer is used to keep the data structures consistent (see
  // requestMoreSpace() for more info, but you should be able to ignore it).
  totalSize = initSize - WORD_SIZE - WORD_SIZE;

  // The heap starts with one free block, which we initialize now.
  firstFreeBlock->sizeAndTags = totalSize | TAG_PRECEDING_USED;
  firstFreeBlock->next = NULL;
  firstFreeBlock->prev = NULL;
  // boundary tag
  *((size_t*)UNSCALED_POINTER_ADD(firstFreeBlock, totalSize - WORD_SIZE)) = totalSize | TAG_PRECEDING_USED;

  // Tag "useless" word at end of heap as used.
  // This is the is the heap-footer.
  *((size_t*)UNSCALED_POINTER_SUB(mem_heap_hi(), WORD_SIZE - 1)) = TAG_USED;

  // set the head of the free list to this new free block.
  FREE_LIST_HEAD = firstFreeBlock;
  return 0;
}


// TOP-LEVEL ALLOCATOR INTERFACE ------------------------------------


//set block allocates the chosen block by removing it from the free list/re-adding the remainder(from mem_sbrk) to the freelist
static void setBlock(BlockInfo * block, size_t reqSize, size_t precedingBlockUseTag ){
  BlockInfo * remainder;
  size_t size_allocated;
  size_allocated = (size_t)SIZE(block->sizeAndTags); //get the size of the block
  removeFreeBlock(block); //if we're allocating, we should remove from the free list
  if( (size_allocated - reqSize) > MIN_BLOCK_SIZE){ //calls to mem_sbrk allocate more memory than we need, let's put back what's left over after filling the request.
    block->sizeAndTags = reqSize | precedingBlockUseTag; //turn on the TAG_PRECEDING_USED for the else clause of mm_malloc
    remainder = (BlockInfo *)UNSCALED_POINTER_ADD(block, reqSize);//reqSize is the payload of the block we're trying to allocate, we move past that portion to access the remainder
    remainder->sizeAndTags = ((size_allocated - reqSize) | TAG_PRECEDING_USED);//the remainder is the block in the list immediately following the allocated. need to 
    //turn on the preceding block used flag
    *((size_t *)UNSCALED_POINTER_ADD(block, (reqSize - WORD_SIZE))) = reqSize;//boundary tag for allocated block
    *((size_t *)UNSCALED_POINTER_ADD(block, (size_allocated - WORD_SIZE))) = (size_allocated - reqSize); //size for the remainder is the size actually allocated - the desired size 
    insertFreeBlock(remainder);//re-insert remainder into the freeList
    
  }

  else{
    *((size_t* )UNSCALED_POINTER_ADD(block,(size_allocated - WORD_SIZE))) = size_allocated;
    remainder = (BlockInfo *)UNSCALED_POINTER_ADD(block, size_allocated);
    remainder->sizeAndTags = remainder->sizeAndTags | TAG_PRECEDING_USED;
  }

  block->sizeAndTags = block->sizeAndTags | TAG_USED;
  block->sizeAndTags = block->sizeAndTags | precedingBlockUseTag;
}

/* Allocate a block of size size and return a pointer to it. */
void* mm_malloc (size_t size) {
  size_t reqSize;
  BlockInfo * ptrFreeBlock = NULL;
  size_t precedingBlockUseTag;
  // Zero-size requests get NULL.
  if (size == 0) {
    return NULL;
  }

  // Add one word for the initial size header.
  // Note that we don't need to boundary tag when the block is used!
  size += WORD_SIZE;
  if (size <= MIN_BLOCK_SIZE) {
    // Make sure we allocate enough space for a blockInfo in case we
    // free this block (when we free this block, we'll need to use the
    // next pointer, the prev pointer, and the boundary tag).
    reqSize = MIN_BLOCK_SIZE;
  } 
  
  else {
    // Round up for correct alignment
    reqSize = ALIGNMENT * ((size + ALIGNMENT - 1) / ALIGNMENT);
  }



  
  ptrFreeBlock = searchFreeList(reqSize); //test for available block
  if(ptrFreeBlock != NULL){ //if block of correct size available:
    precedingBlockUseTag = (ptrFreeBlock)->sizeAndTags & (TAG_PRECEDING_USED); //test to see if block preceeding the block to be allocated is allocated
    setBlock(ptrFreeBlock, reqSize, precedingBlockUseTag);//call to helper function, setBlock
  }

  else{
    requestMoreSpace(reqSize); //request a freeBlock of the appropriate size
    ptrFreeBlock = searchFreeList(reqSize);//search the free list now that we know the free block is there
    precedingBlockUseTag = TAG_PRECEDING_USED;
    setBlock(ptrFreeBlock, reqSize, precedingBlockUseTag);//call to helper function, setBlock


  }
  
  return UNSCALED_POINTER_ADD(ptrFreeBlock, WORD_SIZE);

}

     
     

      
     
     
       
     
   
   
                                                                          
/* Free the block referenced by ptr. */
void mm_free (void *ptr) {
  size_t payloadSize;
  BlockInfo * blockInfo;
  BlockInfo * followingBlock;
  
  blockInfo = (BlockInfo *)UNSCALED_POINTER_SUB(ptr, WORD_SIZE);//header of chosen block to free
  blockInfo->sizeAndTags = blockInfo->sizeAndTags & (~TAG_USED);//turn off the tag used tag
  
  payloadSize = SIZE(blockInfo->sizeAndTags);//get the payload of the block soon to be freed
  followingBlock = (BlockInfo *)UNSCALED_POINTER_ADD(blockInfo, payloadSize + WORD_SIZE);//move to the block that follows the block to be freed
  followingBlock->sizeAndTags = (followingBlock->sizeAndTags) & (~TAG_PRECEDING_USED);//turn off its preceding tag used flag
  insertFreeBlock(blockInfo);//insert block that was freed back to the list
  coalesceFreeBlock(blockInfo);//coalesce, if possible
  
}

//changes the size allocated to a block, if possible
void* mm_realloc(void* ptr, size_t size) {
  size_t oldsize;
  BlockInfo * blockInfo,*block;
  void * copyptr;
 
  if(ptr == NULL && (size > 0)){
    copyptr = mm_malloc(size);
    mm_free(ptr);
  }

  if(size == 0){
    mm_free(ptr);
    copyptr = NULL;
  }
  //code for iterating through the freelist. upon each call of realloc, search the freelist, and coalesce all unused blocks
  //likely inefficent, but sufficient for the project. prevents us from getting a multitude of free blocks that are too big
  //to be used, which causes mem_sbrk to fail and the program to quit.
  for(block = (BlockInfo *)UNSCALED_POINTER_ADD(mem_heap_lo(), WORD_SIZE); /* first block on heap */
      SIZE(block->sizeAndTags) != 0 && block < mem_heap_hi();
      block = (BlockInfo *)UNSCALED_POINTER_ADD(block, SIZE(block->sizeAndTags))) {

    /* and allocated/free specific data */
    if ((block->sizeAndTags & TAG_USED) == 0) {
      coalesceFreeBlock(block);
    } 

  }

  copyptr = mm_malloc(size);//call to mm_malloc for the requested size
  blockInfo = (BlockInfo *)UNSCALED_POINTER_SUB(ptr,WORD_SIZE); //pointer to the header of ptr
  oldsize = SIZE(blockInfo->sizeAndTags);//get the size of ptr
  if(size < oldsize){//if the size of ptr is greater than requested
    oldsize = size;// change the value of bytes to be copied to the requested size  
  }
  memcpy(copyptr, ptr, oldsize); //copy "n = oldsize" bytes from ptr to copyptr
  mm_free(ptr); //return ptr to the freelist
  
  return copyptr; // return copyptr
}

// Implement a heap consistency checker as needed.
//  optional but recommended

int mm_check() {
  return 0;
}

void examine_heap() {
  BlockInfo *block;

  /* print to stderr so output isn't buffered and not output if we crash */
  fprintf(stderr, "FREE_LIST_HEAD: %p\n", (void *)FREE_LIST_HEAD);

  for(block = (BlockInfo *)UNSCALED_POINTER_ADD(mem_heap_lo(), WORD_SIZE); /* first block on heap */
      SIZE(block->sizeAndTags) != 0 && block < mem_heap_hi();
      block = (BlockInfo *)UNSCALED_POINTER_ADD(block, SIZE(block->sizeAndTags))) {

    /* print out common block attributes */
    fprintf(stderr, "%p: %ld %ld %ld\t",
	    (void *)block,
	    SIZE(block->sizeAndTags),
	    block->sizeAndTags & TAG_PRECEDING_USED,
	    block->sizeAndTags & TAG_USED);

    /* and allocated/free specific data */
    if (block->sizeAndTags & TAG_USED) {
      fprintf(stderr, "ALLOCATED\n");
    } else {
      fprintf(stderr, "FREE\tnext: %p, prev: %p\n",
	      (void *)block->next,
	      (void *)block->prev);
    }
  }
  fprintf(stderr, "END OF HEAP\n\n");
}
