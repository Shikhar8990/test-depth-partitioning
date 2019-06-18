Test-Depth Partitioning (TDP)
=============================

A technique to enable distributed symbolic execution built using KLEE.

**Requirements**  
1. Everything that KLEE 3.4 requires http://klee.github.io/releases/docs/v1.4.0/build-llvm34/  
2. Open MPI  
  
**Building Instructions**  
Same as building KLEE 3.4. Clone the repo and follow the instructions for building KLEE 3.4.  
Ofcourse, use this source in place of the original KLEE source.  
  
**Running TDP**  
Following is the list of TDP specific options  
  
-**timeOut**      : serch terminates after timeOut seconds  
-**output-dir**   : Name of the output directory prefix storing the tests. If there are four workers  
                 the name of the directories would be output-dir1, output-dir2, outpit-dir3 and  
                 output-dir4; output-dir0 belongs to the coordinator.  
-**lb**           : flag to enable load balancing (off by default)  
-**phase1Depth**  : number of tests to generate for initial distribution (best to have value same as the number of workers)  
                 should be 0 if using only 1 worker  
-**phase2Depth**  : depth at which to terminate execution   
-**searchPolicy** : search strategy (BFS, DFS or RAND; COVNEW (coverage search - experimental stage))  

**Sample Command**  
The following command launched TDP on program with a bit code file named **prog.bc**.  
TDP is run using 4 worker so we generate 4 initial tests and run it to a timeout of  
1 hour or a depth of 24 (which ever is first).  
The search policy is depth first search.  
Note that when we launch the MPI task using mpirun command, we need two additional cores.  
One of the addtional core acts as a coordinator while the other is used for monitoring and  
is supposed to collect statistics (not yet implemented).  

**mpirun -n 6 /path/to/tdp_build/bin/klee --timeOut=3600 --lb --output-dir=out_prog --phase1Depth=4  
--phase2Depth=24 --searchPolicy=DFS ./prog.bc**

For questions, contact Shikhar - shikhar_singh at utexas dot edu
