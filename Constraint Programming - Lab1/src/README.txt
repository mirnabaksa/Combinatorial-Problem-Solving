For compile instructions on Windows see the report (NOR Logic Synthesis Problem.pdf), section 2.1.

RUNNING:

- one instance:
	./nlsp.exe < in_file > out_file

	where in_file follows the specifications given in the project decription (proj.pdf).

- all instances:
	run the script ./runner.sh

	Runner.sh assumes that all the inputs are in folder ../instances. Outputs are written to ../out

CHECKING OUTPUT:

- one instance:
	./checker.exe < output_file

- all instances:
	run the script ./checker.sh
	
	Checker.sh assumes that the output files are in ../out

CHECKING FOR OPTIMAL OUTPUT:

- all instances:
	./checker_optimal.sh

	Checker_optimal.sh assumes that the output files are in ../out folder and that the path to the results file is ../results.txt.
	
IDEAL DIRECTORY STRUCTURE FOR RUNNING ALL THE SCRIPTS MENTIONED ABOVE:	
 
| instances
|       input files
| out
|		output files   
| src
        checker.cc
        checker.sh
        checker_optimal.sh
        move.sh
        nlsp.cpp
        README.txt
        runner.sh
|	
|  results.txt

        
