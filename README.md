# MIPS-Simulation-using-C
This program simulated the execution of a mips processor. 

Cycle-accurate with respect to register contents.
Simulates a machine consisting of add, sub, addi, mul, lw, sw, beq instructions only.
Will need to provide some error detection wrt the assembly program input.

Instruction Memory: 
Addressed by the PC. 
Size: 2K bytes (512 words).

Data Memory:
Accessible to the program.
Size: 2K bytes (512 words).

Processor
Five stages: IF, ID, EX, MEM, WB

