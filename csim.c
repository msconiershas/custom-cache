/*
 *
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss plus a possible eviction.
 *  2. Instruction loads (I) are ignored.
 *  3. Data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus a possible eviction.
 *
 * The function printSummary() is given to print output.
 * Please use this function to print the number of hits, misses and evictions.
 * This is crucial for the driver to evaluate your work. 
 */

#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include <stdbool.h>


/* Globals set by command line args */
int verbosity = 0; /* print trace if set */
int s = 0; /* set index bits */
int b = 0; /* block offset bits */
int E = 0; /* associativity */
char* trace_file = NULL;

/* Derived from command line args */
int S; /* number of sets S = 2^s In C, you can use the left shift operator */
int B; /* block size (bytes) B = 2^b */

/* Counters used to record cache statistics */
int miss_count = 0;
int hit_count = 0;
int eviction_count = 0;
/*****************************************************************************/


/* Type: Memory address 
 * Use this type whenever dealing with addresses or address masks
 */
typedef unsigned long long int mem_addr_t;

/* Type: Cache line
 */
typedef struct cache_line {
    char valid;
    mem_addr_t tag;
    struct cache_line * next;
} cache_line_t;

typedef cache_line_t* cache_set_t;
typedef cache_set_t* cache_t;


/* The cache we are simulating */
cache_t cache;  

/* 
 * initCache - 
 * Allocate data structures to hold info regrading the sets and cache lines
 * use struct "cache_line_t" here
 * Initialize valid and tag field with 0s.
 * use S (= 2^s) and E while allocating the data structures here
 */
void initCache()
{ 
  //get S
  S = pow(2,s);
 
  //create ian array to hold the sets
  cache = malloc(sizeof(cache_set_t)*S);
  
  //create a pointer to the previous cache line 
  cache_line_t* prev;
 
  for(int i = 0; i < S; i++) {
    	//make a set pointer
    	cache_set_t set;
     
     //allocate the first cache line of the set
    	set  = (cache_set_t) malloc(sizeof(cache_line_t));
    	//mark the valid and tag to be 0
    	set->valid = 0;
    	set->tag = 0;
    	set->next = NULL;
            //make the first line = to prev
    	prev = set;
    	//add the first set to the array of sets
     	cache[i] = set;
      
          	//for each of the remaining lines in each set, set the next
           	for(int j = 1; j < E; j++) {
               //allocate a new line 
          	   cache_set_t line = malloc(sizeof(cache_line_t));
          	   //set this new line as the next for the previous
          	   prev->next = line;	   
          	   //update previous to the new line
          	   prev = line;	  
          	   //mark valid and tag to be 0
          	   line->valid = 0;
          	   line->tag = 0;
          	   line->next = NULL; 
            }
    }
 
}

/* 
 * freeCache - free each piece of memory you allocated using malloc 
 * inside initCache() function
 */
void freeCache()
{
S = pow(2,s);
cache_set_t temp;
for(int i = 0; i < S; i++) {
	cache_set_t start = cache[i];
   while(start->next != NULL) {
	temp = start->next;
	start->next = (start->next)->next;
	free(temp);
   }
   free(cache[i]);
}
free(cache);
}

/* 
 * accessData - Access data at memory address addr.
 *   If it is already in cache, increase hit_count
 *   If it is not in cache, bring it in cache, increase miss count.
 *   Also increase eviction_count if a line is evicted.
 *   you will manipulate data structures allocated in initCache() here
 */
void accessData(mem_addr_t addr)
{  
  //extract s bits
  //first, create mask with 0 for b and t bits and 1 for s bits
  mem_addr_t mask = ((1 << s) - 1) << b;
  
  //AND the mask with the address to get just the s bits
  mem_addr_t m = mask & addr;
  
  //shift s_bits over by b
  int s_bits = m >> b;
  
//get t bits from original address
  mem_addr_t t_bits = addr >> (s+b); 

  cache_set_t line = cache[s_bits];
  
  //to check for matches
  int match = 0;
  
  if(t_bits == line->tag) {
	if(line->valid == 1) {
	match = 1;
	hit_count++;
	}
  }
  int e = E;

  while(!match && e > 1) {

    if(t_bits ==( line->next)->tag) {
        	if((line->next)->valid == 1) {
          	//we have a match!
            match = 1;
        	//increase hit count
        	  hit_count++;
         
        	//move cache line to the front of the list
                //1. first line in set
                cache_set_t next_first = line->next;
                
                //2. get the one that is currently after the one that will be first
                cache_set_t after_next_first = (line->next)->next;
        	
                //3. make the one before the next_first point to the one after next_first
                line->next = after_next_first;
                
                //4. save the address of the current first in the list
                cache_set_t curr_first = cache[s_bits];
        
                //5. make the first line in the cache next_first
                cache[s_bits] = next_first;
        	
                //6. make next_first point to curr_first
                next_first->next = curr_first;
             	
        	break; 
        	}
   }
   //update to next line
   if(line->next != NULL){
  
     line = line->next;
    }	
   e--;
  }
   
   //we didn't find a match
  if(match == 0) {
        cache_set_t check = cache[s_bits];
      	miss_count++;
      	e = 1;

      	if(check->valid == 0)
      		e = 0;

      	//check for any open lines in set (valid = 0)
      	while(e && check->next != NULL && (check->next)->valid == 1 &&  (check->next)->next != NULL) {
      	   check = check->next;
      	}
      	if(!e) {
      	    check->tag = t_bits;
      	    check->valid = 1;    
      	}
      	else if(check->next != NULL && (check->next)->valid == 0) {
   	   
      	    cache_set_t after_next = (check->next)->next;
      	    cache_set_t curr_first = cache[s_bits];
      	     cache[s_bits] = check->next;  
      	    (check->next)->next = curr_first;
      	    (check->next)->tag = t_bits;
      	    (check->next)->valid = 1;    
          	 check->next = after_next;
      	}
      	 else if(check->next == NULL) {//no open lines, must evict
      	
      	     (*check).tag = t_bits;
      	     (*check).valid = 1;   
           	
      	     eviction_count++;
      	 }
         
      	else {
      		eviction_count++;
      		(check->next)->tag = t_bits;
      		(check->next)->valid = 1;
         
	        //save the current first
        	cache_set_t curr_first = cache[s_bits];
      		(check->next)->next = curr_first;
      		cache[s_bits] = check->next;
           check->next = NULL;
      	 	
      	}
}
}

/* 
 * replayTrace - replays the given trace file against the cache 
 * reads the input trace file line by line
 * extracts the type of each memory access : L/S/M
 * one "L" as a load i.e. 1 memory access
 * one "S" as a store i.e. 1 memory access
 * one "M" as a load followed by a store i.e. 2 memory accesses 
 */
void replayTrace(char* trace_fn)
{
    char buf[1000];
    mem_addr_t addr=0;
    unsigned int len=0;
    FILE* trace_fp = fopen(trace_fn, "r");

    if(!trace_fp){
        fprintf(stderr, "%s: %s\n", trace_fn, strerror(errno));
        exit(1);
    }

    while( fgets(buf, 1000, trace_fp) != NULL) {
        if(buf[1]=='S' || buf[1]=='L' || buf[1]=='M') {
            sscanf(buf+3, "%llx,%u", &addr, &len);
      
            if(verbosity)
                printf("%c %llx,%u ", buf[1], addr, len);

          
           // now you have: 
           // 1. address accessed in variable - addr 
           // 2. type of acccess(S/L/M)  in variable - buf[1] 
           // call accessData function here depending on type of access

            if (verbosity)
                printf("\n");
	    //call accessData for the first time
	    accessData(addr);
	    //if we are doing a data modify, call accessData again
	    if(buf[1] == 'M') {
		accessData(addr);
	    }
        }
    }

    fclose(trace_fp);
}

/*
 * printUsage - Print usage info
 */
void printUsage(char* argv[])
{
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}

/*
 * printSummary - Summarize the cache simulation statistics. Student cache simulators
 *                must call this function in order to be properly autograded.
 */
void printSummary(int hits, int misses, int evictions)
{
    printf("hits:%d misses:%d evictions:%d\n", hits, misses, evictions);
    FILE* output_fp = fopen(".csim_results", "w");
    assert(output_fp);
    fprintf(output_fp, "%d %d %d\n", hits, misses, evictions);
    fclose(output_fp);
}

/*
 * main - Main routine 
 */
int main(int argc, char* argv[])
{
    char c;
    
    // Parse the command line arguments: -h, -v, -s, -E, -b, -t 
    while( (c=getopt(argc,argv,"s:E:b:t:vh")) != -1){
        switch(c){
        case 's':
            s = atoi(optarg);
            break;
        case 'E':
            E = atoi(optarg);
            break;
        case 'b':
            b = atoi(optarg);
            break;
        case 't':
            trace_file = optarg;
            break;
        case 'v':
            verbosity = 1;
            break;
        case 'h':
            printUsage(argv);
            exit(0);
        default:
            printUsage(argv);
            exit(1);
        }
    }

    /* Make sure that all required command line args were specified */
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("%s: Missing required command line argument\n", argv[0]);
        printUsage(argv);
        exit(1);
    }

    /* Initialize cache */
    initCache();
 
    replayTrace(trace_file);

    /* Free allocated memory */
    freeCache();

    /* Output the hit and miss statistics for the autograder */
    printSummary(hit_count, miss_count, eviction_count);
    return 0;
}
