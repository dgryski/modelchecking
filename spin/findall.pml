// model for https://utcc.utoronto.ca/~cks/space/blog/programming/GoConcurrencyStillNotEasy

// user configurable values

// number of processes to scan through
#ifndef NUM_PROCESSES
#define NUM_PROCESSES  10
#endif

// concurrency limit; program hangs is LIMIT < NUM_PROCESSES
#ifndef LIMIT
#define LIMIT 4
#endif


chan foundCh = [0] of { bool };
chan limitCh = [LIMIT] of { bool };

proctype find_one_buggy() {
   foundCh ! 0;
   bool x;
   limitCh ? x;
}

inline find_all_buggy() {

	byte i;

	for (i : 1 .. NUM_PROCESSES)  {
	    limitCh ! true;
	    run find_one_buggy();
	}

	bool x;
	for (i : 1 .. NUM_PROCESSES)  {
		 foundCh?x ;
	}
}

// the prosed fixed version to have the goroutines send to limitCh

proctype find_one_fixed_1() {
   limitCh ! true;
   foundCh ! 0;
   bool x;
   limitCh ? x;
}

inline find_all_fixed() {

	byte i;

	for (i : 1 .. NUM_PROCESSES)  {
	    run find_one_fixed_1();
	}

	bool x;
	for (i : 1 .. NUM_PROCESSES)  {
		 foundCh?x ;
	}
}

// the proposed fixed version to have the goroutines send to limitCh before sending to found

proctype find_one_fixed_2() {
   limitCh ! true;
   bool x;
   limitCh ? x;
   foundCh ! 0;
}

inline find_all_fixed_2() {

	byte i;

	for (i : 1 .. NUM_PROCESSES)  {
	    run find_one_fixed_2();
	}

	bool x;
	for (i : 1 .. NUM_PROCESSES)  {
		 foundCh?x ;
	}
}


// the proposed fixed version to have the for loop its own goroutine

proctype find_one_fixed_3() {
   foundCh ! 0;
   bool x;
   limitCh ? x;
}

proctype for_loop() {
	byte i;
	for (i : 1 .. NUM_PROCESSES)  {
	    limitCh ! true;
	    run find_one_buggy();
	}
}


inline find_all_fixed_3() {

	byte i;

	run for_loop();

	bool x;
	for (i : 1 .. NUM_PROCESSES)  {
		 foundCh?x ;
	}
}

init {
    find_all_buggy();
}
