/*
 * mm.c
 *
 * Name: Ashwath Raghav Swaminathan And Shaunak Wagh
 *
 * I'm planning on writing code for the memory initialization function and malloc and coalesce (helper function) for the first commit. The data structure used is Implicit free list(No forward and backward pointers) - for now. - Ashwath

* I just noticed that we are not allowed to use macros. Second commit will convert these macro to static user functions. - Ashwath

* I will be fixing the helper functions in the third commit(Coalesce, find fit and place) - Ashwath
 
 * The algorithm that I'm using for now for finding memory blocks(malloc) to store values is First-Fit Algorithm. (Temp solution) - Ashwath
 
 * For Checkpoint 2, we're going to implement explicit free list(A separate list for storing addresses of free blocks). We're also going to implement a heap checker. 
 
 * Explicit Free list had bad throughput(=0), though utilisation was good(50). Moving to segregated lists to boost throughput!
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
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
 #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16 // For x86-64, we need 16 byte aligned pointers
#define EXTEND_SIZE 4096 // Extend heap by 4k
#define segregatedlist_s 14 // Create 14 segregated lists

// size class of the segregated list
#define seg_class1 32 // store 0 - 32 byte size free blocks in this list
#define seg_class2 64 // store 32 - 64 byte size free blocks in this list
#define seg_class3 128 // store 64 - 128 byte size free blocks in this list
#define seg_class4 256 // store 128 - 256 byte size free blocks in this list
#define seg_class5 512 // store 256 - 512 byte size free blocks in this list
#define seg_class6 1024 // store 512 - 1024 byte size free blocks in this list
#define seg_class7 2048 // store 1024 - 2048 byte size free blocks in this list
#define seg_class8 4096 // store 2048 - 4096 byte size free blocks in this list
#define seg_class9 8192 // store 4096 - 8192 byte size free blocks in this list
#define seg_class10 16384 // store 8192 - 16384 byte size free blocks in this list
#define seg_class11 32768 // store 16384 - 32768 byte size free blocks in this list
#define seg_class12 65536 // store 32768 - 65536 byte size free blocks in this list
#define seg_class13 131072 // store 65536 - 131072 byte size free blocks in this list

typedef void *blk_ptr; // typedef is used to denote void * pointers as random variable blk_ptr

blk_ptr heap_startp = NULL; /* Pointer to first block of memory heap */
blk_ptr segregatedlist[segregatedlist_s]; // create an array of pointers that points to all the segregated lists.

/* Function to determine chunksize - 32k bits[2 power 15] */
static inline size_t chunksize()
{
	
	return(1 << 15);

}

/* Pack function is used to combine the size of memory block and allocated bit into one word */
static inline size_t pack(size_t size,int alloc) 
{
	
	return((size) | (alloc)); /* Size and allocated bit in one word*/
}

/* Function that returns max value - Written to improve readability */

static inline size_t MAX(size_t x,size_t y) 
{
	
	if(x > y)
	return (x);
	else
	return (y);
}

/* Function that returns min value - Written to improve readability */
static inline size_t MIN(size_t x,size_t y)
{
	if(x < y)
	return (x);
	else
	return (y);
}
size_t wordsize = sizeof(void *); /* Wordsize = 8 bytes, word, header and footer size */
size_t doublesize = 2* sizeof(void *); /* Double the Word size */

/* Read and write functions to read or write at address p*/
static inline void writefn(blk_ptr p,size_t val)
{
	
	(*((size_t *)(p)) = (val));

}	
static inline size_t readfn(blk_ptr p) 
{
	
	return(*(size_t *)(p));
}

// make the pointer point to another address - will be useful when adding and removing free blocks from the segregated list. Here, bp points to address of another pointer p
static inline void writeptr(blk_ptr bp, blk_ptr p)
{ 
	*(size_t *)(bp) = (size_t)(p);
}
	
/* Get functions to get the size and allocated fields of memory block at address p*/
static inline size_t  get_size(blk_ptr p)
{
	
	return(size_t)(readfn(p) & ~(doublesize-1));                                                                                                                                    
}
static inline size_t get_alloc(blk_ptr p)
{
	
	return(size_t)(readfn(p) & (0x1));
}

/* Determine the header and footer address of the block pointer bp*/
static inline size_t *headerptr(void *bp)
{
	
	return((size_t *)(bp) - 1);
}
static inline size_t *footerptr(void *bp) 
{
	
	return((size_t *)((bp)+get_size(headerptr(bp))-doublesize));
}

/* Determine the address of the previous and next block*/
static inline size_t *nextblockptr(blk_ptr bp)
{
	
	return((size_t *)((bp)+get_size(headerptr(bp))));
}
static inline size_t *previousblockptr(blk_ptr bp)
{
	
	return((size_t *)((bp)-get_size((bp) - 16)));
}

/* Determine the address of previous and next free block with respect to a pointer in the heap */
static inline size_t *get_previous_freeblock_heap(blk_ptr bp)
{
	return ((size_t *)(bp));
}

static inline size_t *get_next_freeblock_heap(blk_ptr bp)
{
	return ((size_t *)((bp) + 8));
}
/* Determine the next and previous free blocks in the free segregated lists with respect to a pointer belonging to a free list */

static inline size_t * get_next_freeblock_list(blk_ptr bp)
{
	return(*(size_t **)(get_next_freeblock_heap(bp)));
}
static inline size_t * get_previous_freeblock_list(blk_ptr bp)
{
	return(*(size_t **)(bp));
}


/* Helper Functions */

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{

    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/* Determine the segregated list with respect to size [seglist0-seglist13] */
static int search_segregatedlist(size_t size)
{
	if(size < seg_class1)	
	return 0;
	else if((size >= seg_class1) && (size < seg_class2))
		return 1;
	else if((size >= seg_class2) && (size < seg_class3))
		return 2;
	else if((size >= seg_class3) && (size < seg_class4))
		return 3;
	else if((size >= seg_class4) && (size < seg_class5))
		return 4;
	else if((size >= seg_class5) && (size < seg_class6))
		return 5;
	else if((size >= seg_class6) && (size < seg_class7))
		return 6;
	else if((size >= seg_class7) && (size < seg_class8))
		return 7;
	else if((size >= seg_class8) && (size < seg_class9))
		return 8;
	else if((size >= seg_class9) && (size < seg_class10))
		return 9;
	else if((size >= seg_class10) && (size < seg_class11))
		return 10;
	else if((size >= seg_class11) && (size < seg_class12))
		return 11;
	else if((size >= seg_class12) && (size < seg_class13))
		return 12;
	else	
	return 13;
}

/* Add a new free block to the appropriate segregated list */ 
static void insert_freeblock_list(blk_ptr bp,size_t size)
{
	// find the segregated list
    int segregatedlist_ind = search_segregatedlist(size);

	// set head of the size class list
    void *curr_head_ptr = curr_head_ptr = segregatedlist[segregatedlist_ind]; 

 // If there are no blocks in that seg-list
    if (curr_head_ptr != NULL) { 
		// header ptr of the list should now point to bp's address and then we need to update the previous and next block info wrt bp
		segregatedlist[segregatedlist_ind] = bp;
        writeptr(get_previous_freeblock_heap(bp), NULL);
        writeptr(get_next_freeblock_heap(bp), curr_head_ptr);
        writeptr(get_previous_freeblock_heap(curr_head_ptr), bp);
        
    }
	// If there are blocks in that seg-list
    else { 
		// header ptr of the list should now point to bp's address and then we need to update the previous and next block pointers to point to NULL
		segregatedlist[segregatedlist_ind] = bp;
		writeptr(get_previous_freeblock_heap(bp), NULL);
        writeptr(get_next_freeblock_heap(bp), NULL);  
    }
    //mm_checkheap(__LINE__);
} 

/* Remove a free block from the appropriate segregated list */
static void delete_freeblock_list(blk_ptr bp)
{
	// Determine size of the block
	size_t size = get_size(headerptr(bp));

	// Determine the segregated list
	int segregatedlist_ind = search_segregatedlist(size);
	
	if(get_previous_freeblock_list(bp) == NULL){
		// update previous free block pointer 
		if(get_next_freeblock_list(bp) != NULL){
			writeptr(get_previous_freeblock_heap(get_next_freeblock_list(bp)), NULL);
			segregatedlist[segregatedlist_ind] = get_next_freeblock_list(bp);
		}
		else{
			segregatedlist[segregatedlist_ind] = NULL;
		}

	}
	else{
		// update previous free block and next free pointer 
		if(get_next_freeblock_list(bp) != NULL){
			writeptr(get_previous_freeblock_heap(get_next_freeblock_list(bp)), get_previous_freeblock_list(bp));
			writeptr(get_next_freeblock_heap(get_previous_freeblock_list(bp)), get_next_freeblock_list(bp));
			
		}
		else{
			writeptr(get_next_freeblock_heap(get_previous_freeblock_list(bp)), NULL);
		}

	}
	//mm_checkheap(__LINE__);
} 




/* A function to perform Boundary-Tag Coalescing */
// The fn combines free blocks to create one larger block. Used to avoid Internal Fragmentation
static blk_ptr coalesce(void *bp)
{
	
	size_t size = get_size(headerptr(bp));
	size_t previousmem_alloc = get_alloc(headerptr(previousblockptr(bp)));//check if previous block is allocated.
	size_t nextmem_alloc = get_alloc(headerptr(nextblockptr(bp)));// check if next block is allocated.
	
	if(previousmem_alloc && nextmem_alloc) //Case 1 - Previous and Next blocks are allocated - Cannot Coalesce
	{
		return(bp);
	}
	else if(previousmem_alloc && !nextmem_alloc) //Case 2 - Previous block is allocated but next block is not. So we coalesce the next block with other free blocks
	{
		size += get_size(headerptr(nextblockptr(bp)));
		delete_freeblock_list(bp);
		delete_freeblock_list(nextblockptr(bp));
		writefn(headerptr(bp),pack(size,0));
		writefn(footerptr(bp),pack(size,0));
	}
	else if(!previousmem_alloc && nextmem_alloc) //Case 3 - Next block is allocated but previous block is not. So we coalesce the previous block with other free blocks
	{
		size += get_size(headerptr(previousblockptr(bp)));
		delete_freeblock_list(bp);
		delete_freeblock_list(previousblockptr(bp));
		writefn(footerptr(bp),pack(size,0));
		writefn(headerptr(previousblockptr(bp)),pack(size,0));
		bp = previousblockptr(bp);
	}
	else //Case 4 - Both the blocks are free, so we coalesce the next and previous block together.
	{
		size += get_size(headerptr(previousblockptr(bp))) + get_size(footerptr(nextblockptr(bp)));
		delete_freeblock_list(bp);
		delete_freeblock_list(nextblockptr(bp));
		delete_freeblock_list(previousblockptr(bp));
		writefn(footerptr(nextblockptr(bp)),pack(size,0));
		writefn(headerptr(previousblockptr(bp)),pack(size,0));
		bp = previousblockptr(bp);
	}
	insert_freeblock_list(bp,size);
	//mm_checkheap(__LINE__);
	return(bp);
	
	
}

/*When we run out of memory blocks, then we need to extend our memory by 'asize'[computes from align fn] bits(can be any size) to allocate blocks to either variables or constants or some memory objects. */
static blk_ptr extend_heap(size_t words)
{
	size_t asize = align(words);
	size_t *bp;
	
	if((size_t*)(bp = mem_sbrk(asize)) == (void *)-1)
	return (NULL);
	
	// add to segregated list
	insert_freeblock_list(bp,asize);
	
	/* Initialize free blk header and footer*/
	writefn(headerptr(bp),pack(asize,0));
	writefn(footerptr(bp),pack(asize,0));
	writefn(headerptr(nextblockptr(bp)),pack(0,1));
	//mm_checkheap(__LINE__);
	return coalesce(bp); /* Coalesce if previous block is free */
}

/*We have implemented first fit algorithm to find the first fit(it can either be the best fit or it can allocate the first block of size > required block size). Not Optimal */
/*
static void *find_fit(size_t asize)
{
	
	void *bp;
	static int prev_malloc_size = 0;
	static int repeatcounter =0;
	if(prev_malloc_size == (int )asize)
	{
		if(repeatcounter > 30)
		{
			int extendsize = MAX(asize,chunksize());
			bp =extend_heap(extendsize/wordsize);
			return bp;
		}
		else
			{
				repeatcounter++;
			}
	}
	else
	{
		repeatcounter =0;
	}
		for (bp = freelist_startp;get_alloc(headerptr(bp))==0; bp=get_next_freeblock_list(bp))
		{
			if(asize<=(size_t)get_size(headerptr(bp)))
			{
				prev_malloc_size = asize;
				return bp;
			}

		}
		return NULL;
	
	
	for(bp = heap_startp; get_size(headerptr(bp))>0; bp=nextblockptr(bp)) //First fit algorithm - search for the first fit block
	{
		if(!get_alloc(headerptr(bp)) && asize<=get_size(headerptr(bp)))
		return(bp);		
	}
	return NULL; //fit not found - oops!
}
*/

/* To place/write into the allocated memory block */
static blk_ptr place(blk_ptr bp,size_t asize)
{
	delete_freeblock_list(bp);
	size_t csize = get_size(headerptr(bp));
	size_t *next_blk;
	size_t diff = csize-asize;
	if(diff>=(2*doublesize))
	{
		writefn(headerptr(bp),pack(asize,1));
		writefn(footerptr(bp),pack(asize,1));
		next_blk = nextblockptr(bp);
		writefn(headerptr(nextblockptr(bp)),pack(diff,0));
		writefn(footerptr(nextblockptr(bp)),pack(diff,0));
		insert_freeblock_list(nextblockptr(bp), diff);
	}
	else
	{
		writefn(headerptr(bp),pack(csize,1));
		writefn(footerptr(bp),pack(csize,1));
		if(!get_alloc(headerptr(next_blk)))
			writefn(footerptr(next_blk),readfn(headerptr(next_blk)));
	}
	//mm_checkheap(__LINE__);
	return bp;	
}


/*
 * Initialize the heap: returns false on error, true on success.
 */
bool mm_init(void)
{
    for(int i = 0; i < segregatedlist_s; i++)
    {
		segregatedlist[i] = NULL; //initialize the pointers to all lists
    }
		
    if ((heap_startp = mem_sbrk(4 * wordsize)) == NULL) //Heap Size - 32 bytes
    return false;
    
    writefn(heap_startp,0); /* For Alignment */
    writefn(heap_startp+(1*wordsize),pack(doublesize,1)); /* Prologue Header*/
    writefn(heap_startp+(2*wordsize),pack(doublesize,1)); /* Prologue Footer */
    writefn(heap_startp+(3*wordsize),pack(0,1)); /* Epilogue Header */
    
    
    /* We have an empty heap, so extend it by 4096 bits/512 bytes*/
    if(extend_heap(chunksize()/wordsize)==NULL)
    return false;
    
    //mm_checkheap(__LINE__);
    return true; 
}

/*
 * malloc - We are performing both malloc and find fit in malloc by employing best fit algorithm.
 */
void* malloc(size_t size)
{
	

    size_t asize; // Adjust the size of the block
    size_t extendsize; /* If there's no fit, then extend the heap size by extendsize */
    blk_ptr bp = NULL;
    int segregatedlist_ind = 0;
    
    if (size == 0)/* Ignore these requests as per pdf document(Size can't be 0) */
    return (NULL);
    
    if (size <= doublesize)
    asize = 2 * doublesize; //Adjust the block size to include overhead(allocated bits,etc) and alignment.
    
    else
    asize = align(size+doublesize); //Adjust the block size to include overhead(allocated bits,etc) and alignment.
    
    // Determine the segregated list
	segregatedlist_ind = search_segregatedlist(asize);
	// Determine how much the heap should be extended
	extendsize = MAX(asize, EXTEND_SIZE);

	// find fit algorithm
	if(segregatedlist_ind != segregatedlist_s){
		bp = segregatedlist[segregatedlist_ind];
		if(bp != NULL){
			for(int i = 0; i < 32 ; i++){
				if(bp == NULL){
					break;
				}
				if(asize <= get_size(headerptr(bp))){
					place(bp,asize);
					//mm_checkheap(__LINE__);
					return bp;
				}
				bp = get_next_freeblock_list(bp);
			}
		}
	}

	segregatedlist_ind++;
	bp = NULL;
	
	// if there is no room in the list, then allocate more memory in heap.
	while((segregatedlist_ind < segregatedlist_s) && (bp == NULL)){
		bp = segregatedlist[segregatedlist_ind];
		segregatedlist_ind++;
	}
	
	if(bp == NULL){
		bp = extend_heap(extendsize);
	}

	bp = place(bp,asize);
	//mm_checkheap(__LINE__);
	return bp;
}

/*
 * free
 */
// Freeing the memory blocks
void free(void* ptr)
{
 
    size_t size;      //We initialize size to hold the size of the block

    if(ptr == NULL)        // When pointer is NULL, which means it does not point to a block 
        return;
    size = readfn(headerptr(ptr));  // we get the size of block and store it in size 
    writefn(headerptr(ptr),pack(size,0)); // we are freeing header of the block by writing it to 0
    writefn(footerptr(ptr),pack(size,0));	// we are freeing footer of the block by writing it to 0
    insert_freeblock_list(ptr,size);  // We are adding the pointer of the newly free block to segregated list
    coalesce(ptr); // we send the pointer to coalesce all the free blocks by sending the free block pointer
    
    //mm_checkheap(__LINE__);
}

/*
 * realloc
 */
// Reallocation the memory
void* realloc(void* oldptr, size_t size)
{
    

    
    blk_ptr nptr; // initialize the a new pointer for reallocated memory
    
    
    if(oldptr == NULL){           	//When the old pointer is NUll, which means the block is not allocated and therefore can be sent to malloc to allocate the free block
	//mm_checkheap(__LINE__);
        return(malloc(size));

    }
    if(size == 0){				//When size is 0, this means we not reallocating any memory size to allocated block and instead it can be sent to free to free the block

        free(oldptr);
        //mm_checkheap(__LINE__);
        return(NULL);
    }
    

    nptr = malloc(size); // we malloc the memory of size to a free block and set the new pointer to newly allocated block
    size_t newsize = MIN(size,get_size(headerptr(oldptr))-wordsize); // We find the minimium size of both new size of block and the old size of block by old pointer
    memcpy(nptr,oldptr,newsize);// we copy the data of old block to new block
    free(oldptr);//free the old block point to a free block
    //mm_checkheap(__LINE__);
    return nptr;// we return newly reallocated block pointer

    
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
	
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    //mm_checkheap(__LINE__);
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
	
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{

    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{

#ifdef DEBUG
	printf("We have entered checkheap\n");
    size_t size = 0;
    heap_startp = mem_heap_lo() + 2*wordsize;   // we check the size of block
    while (get_size(headerptr(heap_startp)) != 0){
		
        size = get_size(headerptr(heap_startp));
        if (size != get_size(footerptr(heap_startp))){
            printf("The Header and Footer are not matching in line no : %d\n",lineno); //header size and footer size should match
        }

        
        if (!get_alloc(headerptr(heap_startp))){
            if (!get_alloc(headerptr(nextblockptr(heap_startp)))){ // checking if the memory heap is contiguous by finding the next block 
                printf("We have found the next block \n");
            }
        }

        heap_startp = heap_startp + size;
    }

	#endif /* DEBUG */
    return true;
}


