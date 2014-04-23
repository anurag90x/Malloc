/*
 * This implementation replicates the implicit list implementation
 * provided in the textbook
 * "Computer Systems - A Programmer's Perspective"
 * Blocks are never coalesced or reused.
 * Realloc is implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
		/* Team name */
		"Red Bull",
		/* First member's full name */
		"Orkhan Karimov ",
		/* First member's email address */
		"orkhan.karimov@mail.utoronto.ca",
		/* Second member's full name (leave blank if none) */
		"Anurag Chaudhury",
		/* Second member's email address (leave blank if none) */
		"anurag.chaudhury@mail.utoronto.ca"
};

/*************************************************************************
 * Basic Constants and Macros
 * You are not required to use these macros but may find them helpful.
 *************************************************************************/
#define WSIZE       sizeof(void *)         /* word size (bytes) */
#define DSIZE       (2 * WSIZE)            /* doubleword size (bytes) */
#define CHUNKSIZE   (1<<7)      /* initial heap size (bytes) */
#define OVERHEAD    DSIZE     /* overhead of header and footer (bytes) */

#define MAX(x,y) ((x) > (y)?(x) :(y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(uintptr_t *)(p))
#define PUT(p,val)      (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* alignment */
#define ALIGNMENT 16
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0xf)
//number of lists
#define TABLESIZE 33
// Could have chosen 256 as well for the same performance, we chose it since its multiple of 16
#define MINSIZE 128

void* heap_listp = NULL;
void *extend_heap(size_t words);
int calc_index (int size);
void *table_head = NULL;
void* split (void*bp,  size_t asize);
/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
int mm_init(void)
{

	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_listp, 0);                         // alignment padding
	PUT(heap_listp + (1 * WSIZE), PACK(OVERHEAD, 1));   // prologue header
	PUT(heap_listp + (2 * WSIZE), PACK(OVERHEAD, 1));   // prologue footer
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header
	heap_listp += DSIZE;

	void *temp;
	int seg_list_size = TABLESIZE*WSIZE;
	int seg_list_alloc = DSIZE * ((seg_list_size + (OVERHEAD) + (DSIZE-1))/ DSIZE);
	//printf ("size %d, alloc size %d\n", seg_list_size, seg_list_alloc);

	size_t words =  seg_list_alloc/WSIZE;

	/* Allocate an even number of words to maintain alignments */
	int size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ( (temp = mem_sbrk(size)) == (void *)-1 )
		return NULL;


	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(temp), PACK(size, 1));                // free block header
	PUT(FTRP(temp), PACK(size, 1));                // free block footer
	PUT(HDRP(NEXT_BLKP(temp)), PACK(0, 1));        // new epilogue header



	table_head = temp;

	int i;

	for (i=0; i<TABLESIZE;i++) {
		PUT(table_head+i*WSIZE, NULL);

	}


	return 0;
}

/**********************************************************
 * coalesce
 * Covers the 4 cases discussed in the text:
 * - both neighbours are allocated
 * - the next block is available for coalescing
 * - the previous block is available for coalescing
 * - both neighbours are available for coalescing
 **********************************************************/


void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // allocation bit of previous block
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // allocation bit of next block
	size_t size = GET_SIZE(HDRP(bp)); // size of present block


	if (prev_alloc && next_alloc) { 
	      
                    /* Case 1  - neither are free*/
		int temp_index = calc_index (size);
		void *temp_head_list = table_head+temp_index*WSIZE;

		add_node (HDRP(bp), temp_head_list); // add node to free list
		return (bp);
	}

	else if (prev_alloc && !next_alloc) { 

                    /* Case 2 - prev is allocated and next is free*/
		size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // increment size by size of the next block

		PUT(bp, GET(NEXT_BLKP(bp))); // add pointer to next-next block
		PUT(bp+WSIZE, GET(NEXT_BLKP(bp)+WSIZE)); // add pointer to next-previous block

		int temp_size = GET_SIZE(HDRP(NEXT_BLKP(bp))); // get size of next block
		int temp_index = calc_index (temp_size);
		void *temp_head_list = table_head+temp_index*WSIZE; // get the correct head
		delete_node(HDRP(NEXT_BLKP(bp)), temp_head_list);

		PUT(HDRP(bp), PACK(size, 0)); // free the block
		PUT(FTRP(bp), PACK(size, 0)); //free the block

		temp_index = calc_index (size);
		temp_head_list = table_head+temp_index*WSIZE;
		add_node (HDRP(bp), temp_head_list);
		return (bp);
	}

	else if (!prev_alloc && next_alloc) { 
	
                    /* Case 3  - prev is free and next is allocated*/
		size += GET_SIZE(HDRP(PREV_BLKP(bp))); // increment by size of prev block

		int temp_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
		int temp_index = calc_index (temp_size);
		void *temp_head_list = table_head+temp_index*WSIZE;
		delete_node(HDRP(PREV_BLKP(bp)), temp_head_list); // delete previous node from free list

		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

		temp_index = calc_index (size);
		temp_head_list = table_head+temp_index*WSIZE;
		add_node (HDRP(PREV_BLKP(bp)), temp_head_list);
		return PREV_BLKP(bp);

	}

	else {            
	          /* Case 4 - both are free*/
		size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
				GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;

                    // delete both nodes from respective free lists
                    
		int temp_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
		int temp_index = calc_index (temp_size);
		void *temp_head_list = table_head+temp_index*WSIZE;
		delete_node(HDRP(PREV_BLKP(bp)), temp_head_list);

		temp_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
		temp_index = calc_index (temp_size);
		temp_head_list = table_head+temp_index*WSIZE;
		delete_node(HDRP(NEXT_BLKP(bp)), temp_head_list); 

		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));

		temp_index = calc_index (size);
		temp_head_list = table_head+temp_index*WSIZE;
		add_node (HDRP(PREV_BLKP(bp)), temp_head_list);

		return (PREV_BLKP(bp));
	}




}


/**********************************************************
 * add_node
 * parameters - pointer to block (*bp),pointer to head of list that contains that block(*head)
 * function to add a node to the appropriate free list
 **********************************************************/


void add_node(void *bp, void *head)
{
          // add to beginning of list if list is null
	if (GET(head) == NULL)
	{

		PUT(head, bp);

		PUT(bp+2*WSIZE,NULL);

		PUT(bp+WSIZE, NULL);

	}



	else {
                    // if list is not null add to the beginning of list

		void * temp = GET(head); //get the head

		PUT(head, bp); 
		PUT(bp+2*WSIZE,NULL);
		PUT(bp+WSIZE, temp);
		PUT(temp+2*WSIZE, bp);


	}




}

/**********************************************************
 * delete_node
 * parameters - pointer to block (*bp),pointer to head of list that contains that block(*head)
 * function to delete a node from the appropriate free list
 **********************************************************/
void delete_node (void *bp, void *head)
{

	void* next_node = GET(bp+WSIZE); //pointer to next node
	void* prev_node = GET(bp+2*WSIZE); //pointer to previous node

          // Delete first node from list
	if (prev_node == NULL)
	{
                    // if only one element in the list
		if (next_node == NULL) {

			PUT (head, NULL);

		}
                    // if next not null (more than one element in the list)
		else if (next_node != NULL) {
			PUT(head, next_node);
			PUT(next_node+2*WSIZE, NULL);

		}

	}
          // any node in the middle of the list
	else if (next_node != NULL && prev_node != NULL )
	{

		PUT(prev_node+WSIZE, next_node);
		PUT(next_node+2*WSIZE, prev_node);

	}
          // the last node in the list
	else if (next_node == NULL && prev_node != NULL)
	{

		PUT(prev_node+WSIZE, NULL);

	}
          //resetting the pointers for the free block
	PUT(bp+WSIZE, NULL); 
	PUT(bp+2*WSIZE, NULL);


}

/**********************************************************
 * extend_heap
 * Extend the heap by "words" words, maintaining alignment
 * requirements of course. Free the former epilogue block
 * and reallocate its new header
 **********************************************************/
void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignments */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ( (bp = mem_sbrk(size)) == (void *)-1 ) {

		return NULL;
	}

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));                // free block header
	PUT(FTRP(bp), PACK(size, 0));                // free block footer
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));        // new epilogue header



    return bp;

}
/**********************************************************
 * find_fit
 * Traverse the heap searching for a block to fit asize
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
void * find_fit(size_t asize)
{

	void *bp;

	int index = calc_index(asize); // index for the particular size

	int i; // loop variable

	for (i=index; i<TABLESIZE; i++) {
		void* list_head = (table_head+i*WSIZE);  // the right bin
                    // loop through the nodes in the list
                 
		for (bp = GET(list_head); bp != 0; bp = GET(bp + WSIZE))
		{

			if (asize <= GET_SIZE((bp))) // find right size
			{
                                        // if the same size, then pick out from the list and return
				if (asize == GET_SIZE((bp)))
				{
					delete_node(bp, list_head);
					return bp+WSIZE;
				}
				else {
				          //Since size is greater we can split and add the remainder to free list
					delete_node (bp, list_head);
					void *temp = split (bp, asize);
					return temp+WSIZE; }

			}
		}
	}

	return NULL; // could not find any free node in any of the lists. Need to extend heap in this case.
}

/**********************************************************
 * split
 * Parameters - poitner to block (*bp) and size to split (asize)
 * Split the block into the block that will be allocated and a free
 * chunk that can be added back to one of the free lists.
 **********************************************************/
void* split ( void*bp,  size_t asize)
{

	int delta_size = GET_SIZE(bp) - asize; // difference between sizes

	if (delta_size>=2*DSIZE) {
	          // only makes sense to split if the difference is greater than 2 words because that is the min.block
	          // size

		void *temp_head; 
		void * new_block = bp+delta_size;

		int total_size = GET_SIZE(bp); // size of present block


		PUT(bp, PACK(delta_size,0)); //change the size
		PUT(bp+delta_size-WSIZE, PACK(delta_size,0));//add a new footer


		PUT(bp+delta_size, PACK(asize,0)); //new header
		PUT(bp+total_size-WSIZE, PACK(asize, 0)); // modified footer

		int index = calc_index(GET_SIZE(bp)); //find the correct list to insert new free block to

		temp_head = (table_head+index*WSIZE); // head pointer for the appropriate bin.

		add_node (bp, temp_head); // add the node to that list
                   
                    // return the pointer to the to be allocated block
		return new_block;
	}
          // if split not possible just return pointer to original block
	return bp;
}
 
/**********************************************************
 * place
 * Mark the block as allocated
 **********************************************************/
void place(void* bp, size_t asize)
{
          
	size_t bsize = GET_SIZE(HDRP(bp));
          // Mark as allocated

	PUT(HDRP(bp), PACK(bsize, 1));
	PUT(FTRP(bp), PACK(bsize, 1));

}

/**********************************************************
 * calc_index
 * Find the right bin to place the block
 **********************************************************/
int calc_index (int size)
{

	int index = -1;

	if ( size<=MINSIZE) {

		index = size/DSIZE-1;

	}

	else if (size>MINSIZE && size<=2*MINSIZE)
		index = 16;

	else if (size>2*MINSIZE && size<=4*MINSIZE)
		index = 17;

	else if (size>4*MINSIZE && size<=8*MINSIZE)
		index = 18;

	else if (size>8*MINSIZE && size<=12*MINSIZE)
		index = 19;

	else if (size>12*MINSIZE && size<=16*MINSIZE)
		index = 20;

	else if (size>16*MINSIZE && size<=20*MINSIZE)
		index = 21;

	else if (size>20*MINSIZE && size<=24*MINSIZE)
		index = 22;

	else if (size>24*MINSIZE && size<=28*MINSIZE)
		index = 23;

	else if (size>28*MINSIZE && size<=32*MINSIZE)
		index = 24;

	else if (size>32*MINSIZE && size<=36*MINSIZE)
		index = 25;

	else if (size>36*MINSIZE && size<=40*MINSIZE)
		index = 26;

	else if (size>40*MINSIZE && size<=60*MINSIZE)
		index = 27;

	else if (size>60*MINSIZE && size<=120*MINSIZE)
		index = 28;

	else if (size>120*MINSIZE && size<=200*MINSIZE)
		index = 29;

	else if (size>200*MINSIZE && size<=400*MINSIZE)
		index = 30;

	else if (size>400*MINSIZE && size<=4000*MINSIZE)
		index = 31;

	else
		index = 32;



          // Return the correct index
	return index;
}


/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{

	if(bp == NULL){
		return;
	}

	size_t size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size,0));
	PUT(FTRP(bp), PACK(size,0));

	bp = coalesce(bp);




}


/**********************************************************
 * mm_malloc
 * Allocate a block of size bytes.
 * The type of search is determined by find_fit
 * The decision of splitting the block, or not is determined
 *   in place(..)
 * If no block satisfies the request, the heap is extended
 **********************************************************/
void *mm_malloc(size_t size)
{

	size_t asize; /* adjusted block size */
	size_t extendsize; /* amount to extend heap if no fit */
	char * bp;

	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = DSIZE + OVERHEAD;
	else
		asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1))/ DSIZE);




	/* Search the free list for a fit */

	if ((bp = find_fit(asize)) != NULL) {

		place(bp, asize);

		return bp;
	}

	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize, CHUNKSIZE);


	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;

	if (asize == GET_SIZE((HDRP(bp))))

	{
		place(bp, asize);
		return bp;
	}


	else if (asize < GET_SIZE((HDRP(bp)))) {
		void *temp = split (bp-WSIZE, asize);

		place(temp+WSIZE, asize);
		return temp+WSIZE;
	}

}






/**********************************************************
 * mm_realloc
 * Similar to naive malloc however if the new size is less than
 * original size, we split the block and if the new size is greater we
 * coalesce with other blocks
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{

	if (size == 0){
		mm_free(ptr);
		return NULL;
	}

	/* If old ptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	void *oldptr = ptr;
	void *newptr;
	size_t oldSize, copySize;




	/* Copy the old data. */
	

	oldSize = GET_SIZE(HDRP(oldptr));
          
          // the new size is less than old size but the difference is more than 32
	if (size+DSIZE < oldSize && (oldSize-(size+DSIZE))>2*DSIZE)
	{
                    // get the adjusted size (after overhead and alignment)
		if (size <= DSIZE)
			size = DSIZE + OVERHEAD;
		else
			size = DSIZE * ((size + (OVERHEAD) + (DSIZE-1))/ DSIZE);

                    // split the block
		PUT(HDRP(oldptr),PACK(size,1));
		PUT(FTRP(oldptr),PACK(size,1));

		newptr = oldptr;

		oldptr = NEXT_BLKP(newptr);
		PUT(HDRP(oldptr),PACK(oldSize-size,0));
		PUT(FTRP(oldptr),PACK(oldSize-size,0));
          
                    // coalesce the free block
		//coalesce(oldptr);
                    // return pointer to new block
		return newptr;


	}
	// if we cannot split then just return pointer to the old block
	else if (size+DSIZE < oldSize && !((oldSize-(size+DSIZE))>(2*DSIZE)))
	{
		return oldptr;

	}


	else {
	          // the new size is greater than the original size

                    // get adjusted size
		if (size <= DSIZE)
			size = DSIZE + OVERHEAD;
		else
			size = DSIZE * ((size + (OVERHEAD) + (DSIZE-1))/ DSIZE);

		void * next_block = NEXT_BLKP(ptr);
		int total_size = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(next_block));

		// Check if next block is free
		if (GET_ALLOC(HDRP(next_block)) == 0)
		{

			if (total_size >= size)
			{         
                                        // going to coalesce the present block and the next block
				int finalSize = GET_SIZE(HDRP(ptr));
				finalSize += GET_SIZE(HDRP(NEXT_BLKP(ptr)));


				int temp_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
				int temp_index = calc_index (temp_size);
				void *temp_head_list = table_head+temp_index*WSIZE;
				delete_node(HDRP(NEXT_BLKP(ptr)), temp_head_list); // delete next block from free list

				PUT(HDRP(ptr), PACK(finalSize, 0));
				PUT(FTRP(ptr), PACK(finalSize, 0));
                                                 
                                        // can split the coalesced block
				if (total_size-size>2*DSIZE) {

                                                  // splitting the coalesced block

					void *last = FTRP(ptr);

					PUT(HDRP(ptr), PACK(size,0));
					PUT(FTRP(ptr), PACK(size,0));

					PUT(FTRP(ptr)+WSIZE, PACK(total_size-size, 0));
					PUT(last, PACK(total_size-size,0));

					int temp_size2 = GET_SIZE(FTRP(ptr)+WSIZE);
					int temp_index2 = calc_index (temp_size2);
					// insert the split free block to appropriate list
					void *temp_head_list2 = table_head+temp_index2*WSIZE;
					add_node(FTRP(ptr)+WSIZE, temp_head_list2);
					
					

                                                  // allocate the split to be used block

					place(ptr, size);
					return ptr;

				}

				else /*if (total_size == size) */
						{

					                    place(ptr, size);
					                    return ptr;

						}


			}


		}


                    // if the size is greater than the total size we need to malloc and memcpopy

		


	}
          newptr = mm_malloc(size);
		if (newptr == NULL)
			return NULL;
	copySize = GET_SIZE(HDRP(oldptr));
	if (size < copySize)
		copySize = size;
	memcpy(newptr, oldptr, copySize);
	mm_free(oldptr);
	return newptr;
}


/**********************************************************
 * mm_check
 * Check the consistency of the memory heap
 * Return nonzero if the heap is consistant.
 *********************************************************/
int mm_check(void){


	// Is every block in free list marked as free?
	int index;
	void* list_head;
	void *temp;
	void *temp2;
	void *lo = mem_heap_lo();
	void *hi = mem_heap_hi();

	for (index = 0; index<TABLESIZE; index++)
	{
		list_head = table_head+index*WSIZE;
		for (temp = GET(list_head); temp != 0; temp = GET(temp + WSIZE))
		{
			if (GET_ALLOC(temp) == 1)
			{
				printf ("Block in free list is not marked free\n");
				return -1;
			}
		}
	}

	// Are there any contagious free blocks that somehow escaped coalescing?

	temp = heap_listp;
	while(NEXT_BLKP(temp)-1 != mem_heap_hi())
	{
		if (GET_ALLOC(HDRP(temp)) == 0 && GET_ALLOC(HDRP(NEXT_BLKP(temp)))==0)
		{
			printf ("There are contagious free blocks that somehow escaped coalescing\n");
			return -1;
		}

		temp = NEXT_BLKP(temp);

	}

	// Is every free block actually in the free list?
	temp2 = heap_listp;

	while(NEXT_BLKP(temp2)-1 != mem_heap_hi() )
	{
		if (GET_ALLOC(HDRP(temp2)) == 0)
		{  int done=0;

		for (index = 0; index<TABLESIZE && !done; index++)
		{
			list_head = table_head+index*WSIZE;
			for (temp = GET(list_head); temp != 0; temp = GET(temp + WSIZE))
			{
				if (GET_SIZE(temp) == GET_SIZE(HDRP(temp2)) && temp==temp2-WSIZE)
				{ done = 1;

				}

			}
		}

		if (done == 0)
		{
			printf ("There is a free block which is not actually in the free list");
			return -1;
		}
		}

		temp2 = NEXT_BLKP(temp2);

	}


	// Do the pointers in the free list point to valid heap address?
	for (index = 0; index<TABLESIZE; index++)
	{
		list_head = table_head+index*WSIZE;
		for (temp = GET(list_head); temp != 0; temp = GET(temp + WSIZE))
		{
			if (temp < lo || temp >hi)
			{
				printf ("Pointers in the free list does not point to valid heap address\n");
				return -1;
			}

		}
	}


	// Is all pointers in heap are valid?
	temp2 = heap_listp;

	while(NEXT_BLKP(temp2)-1 != mem_heap_hi() )
	{

		if (temp2 < lo || temp2 >hi)
		{
			printf ("Pointers in the heap block does not point to valid heap address\n");
			return -1;
		}


		temp2 = NEXT_BLKP(temp2);

	}




	return 1;




}

