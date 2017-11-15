
// List the full names of ALL group members at the top of your code.
// SuoAn Gao, Yujia Huo, SiyuWu

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>
# include <ctype.h>
# include <stdbool.h>

//feel free to add here any additional library names you may need
#define SINGLE 1
#define BATCH 0
#define REG_NUM 32

//stage is doing useful work
long IF_cycle=0;
long ID_cycle=0;
long EX_cycle=0;
long MEM_cycle=0;
long WB_cycle=0;

// total cycle
long total_IF_cycle=0;
long total_ID_cycle=0;
long total_EX_cycle=0;
long total_MEM_cycle=0;
long total_WB_cycle=0;

int flagofEnd=0;
int IF_end=0;
int ID_end=0;
int EX_end=0;
int MEM_end=0;
enum opcodeEnum {add, addi, sub, mul, beq, lw, sw, haltSimulation};
long pgm_c=0;//time 4 or not？？？？？？？？？？？？？？？？？？？？？？？？
long temp_MEM;
/**************************/
bool HzRawFlag;// flag up if raw detected
/**************************/

struct inst {
	enum opcodeEnum opcode;
	int rs;
	int rt;
	int rd;
	int Imm;
	long IC;
};
char instrc[40];

struct latch {
	struct inst instruction;
	int valid;//1 for the content in the latch has not been read by the stage after it
	//0 for the content in the latch has already been read by the stage after it
	//reset this bit at the first cycle when the stage after this latch starts doing a new instruction
	//set this bit at the last cycle when the stage before this latch does one instruction
	//only when valid bit is 1, the stage after this latch can do the new instruction in this latch
	//otherwise, the stage after this latch has to wait for a new instruction
	int branch;//for IF_ID_latch, 0 for no branch detected in ID
	//or the branch is solved in MEM. IF can get the inst that PC points
	int free;//1 for later stage has already finished
	//only when all latches free field are 1, we can start enter the next stage
	//otherwise, wait
	int pass;
	int prevPass;
	long SourceVal1; // value of rs
	long SourceVal2;  // value of rt
	long ResutVal;
	//long prevFree; // vallue of previous Free.
	long prevBranch; // value of previous branch
};

//int move;//1 for all stages have finished, we can move to the next instruction
struct latch IF_ID_latch;

struct latch ID_EX_latch;

struct latch EX_MEM_latch;

struct latch MEM_WB_latch;

struct latch PC_latch;//the latch before IF

//code from https://en.wikibooks.org/wiki/C_Programming/string.h/
int my_strcmp (const char * s1, const char * s2)
{
    for(; *s1 == *s2; ++s1, ++s2)
        if(*s1 == 0)
            return 0;
    return *(unsigned char *)s1 < *(unsigned char *)s2 ? -1 : 1;
}

char *my_strcat(char *dest, const char *src)
{
    size_t i,j;
    for (i = 0; dest[i] != '\0'; i++)
        ;
    for (j = 0; src[j] != '\0'; j++)
        dest[i+j] = src[j];
    dest[i+j] = '\0';
    return dest;
}

struct inst initInst(struct inst Inst) {
	Inst.opcode=-1;
	Inst.rs=-1;
	Inst.rt=-1;
	Inst.rd=-1;
	Inst.Imm=-1;
	Inst.IC=-1;
	return Inst;
}
void printInstruction(struct inst Inst) {
	printf("@@@@@@@ printInstruction @@@@@@@@\n");
	printf("IC=%ld\n",Inst.IC);
	printf("opcode=%d\n",Inst.opcode);
	printf("rs=%d\n",Inst.rs);
	printf("rt=%d\n",Inst.rt);
	printf("rd=%d\n",Inst.rd);
	printf("Imm=%d\n",Inst.Imm);
	printf("@@@@@@@ printInstruction @@@@@@@@\n");

}
void IF(struct inst *IMEM, int c) {
	assert(c>0);
	static long IMEM_cycle_counter=0;
	//printf("IF: ID_end=%d\n", IF_end);
	if(!IF_end) { //IMEM[pgm_c].opcode!=haltSimulation){//when the last one occurs,do not enter IF, and do not increment total_IF_cycle
		total_IF_cycle++;

		if((IF_ID_latch.branch==0)&&((IF_ID_latch.prevPass==1)||(PC_latch.free==0))) { //no branch needed to wait
			//printf("IF:  doing  work!\n");
			//The ID has already finished its current task, the task in IF can pass to ID
			//IF can handle the next instruction

			if(IMEM[pgm_c].opcode!=haltSimulation) {
				if(IMEM_cycle_counter==0) {
					//printf("IF:  start new work!    ");
					//printf("IF: new work pc: %ld\n", pgm_c);
					PC_latch.free=0;//IF stage started doing its this task
				}
				IMEM_cycle_counter++;
				//printf("IF: IMEM_cycle_counter: %ld\n", IMEM_cycle_counter);
				if(IMEM_cycle_counter==c) { //it takes c cycles to solve IF
					//printf("IF:  finishing  work!   ");
					//printf("IF: finishing work pc: %ld\n", pgm_c);
					IF_ID_latch.instruction=IMEM[pgm_c];//The next instruction that ID should handle
					pgm_c++;//in this simulation, do not excute until the last cycle
					PC_latch.free=1;//IF is finished
					IF_cycle += c;
				}
			} else {
				//printf("IF: meet halt!!!!!!!!!!!!!!!!!!!!\n");
				IF_end=1;
				IMEM_cycle_counter=c;
				IF_ID_latch.instruction=IMEM[pgm_c];
				IF_ID_latch.valid=1;
			}
		}
		//printf("IF_ID_latch.pass: %d\n",IF_ID_latch.pass);
		if((IF_ID_latch.free == 1)&&(IMEM_cycle_counter==c)) {
			//printf("IF: about doing new work!  ");
			//printf("IF: new work pc: %ld\n", pgm_c);
			IF_ID_latch.valid=1;
			IMEM_cycle_counter=0;

			//IF_ID_latch.instruction=IMEM[pgm_c];
		}
	} else {
		IF_ID_latch.valid=1;
	}//else{
	// IF_ID_latch.instruction=IMEM[pgm_c];

}


void ID(struct inst *IMEM,long *mips_reg ) {
	static long ID_cycle_counter=0;
	static struct inst currentInstruction;
	static int hazard=0;
	//printf("ID:ID_end=%d\n", ID_end);
	if(!ID_end) { //(IF_ID_latch.instruction.opcode==haltSimulation)){// make it is not the last instruction
		//printf("ID: IF_ID_latch.valid: %d ID_EX_latch.prevPass: %d IF_ID_latch.free: %d IF_ID_latch.pass: %d\n", IF_ID_latch.valid,ID_EX_latch.prevPass, IF_ID_latch.free,IF_ID_latch.pass  );
		total_ID_cycle++;
		////printf();
		if((IF_ID_latch.valid == 1)&&((ID_EX_latch.prevPass == 1)||(IF_ID_latch.free==0)||(IF_ID_latch.pass==1))) { // if the later latch ID_EX hasn't finished the job, ID wait till it's done, and add total cycle
			//printf("ID: have a new work!\n");
			if(hazard==0) {
				//ID_EX_latch.instruction=IF_ID_latch.instruction;//.opcode = IF_ID_latch.instruction.opcode;
				currentInstruction=IF_ID_latch.instruction;
			}
			IF_ID_latch.pass=0;
			if(currentInstruction.opcode!=haltSimulation) {
				if(IF_ID_latch.instruction.opcode==beq) {
					IF_ID_latch.branch=1;
				}
				IF_ID_latch.free=0;
				// Generally we pass instruction to the next latch

				hazard=0;
				/*  //ID_EX_latch.instruction.rs = IF_ID_latch.instruction.rs;
				 //ID_EX_latch.instruction.rt = IF_ID_latch.instruction.rt;
				//ID_EX_latch.instruction.rd = IF_ID_latch.instruction.rd; */
				/******************** IF current instructions are BEQ ADD SUB MUL SW ***********************/
////////////////////////////////////////////////////////////////////////////////////////////////////
				if((currentInstruction.opcode == beq) || (currentInstruction.opcode == add) || (currentInstruction.opcode == sw)
				        || (currentInstruction.opcode == sub) || (currentInstruction.opcode == mul)) {
					// if cur instructions are add sub beq mul sw
					//printf("ID: current is  add sub beq mul sw!   ");
					//printf("ID: new work pc: %ld\n", currentInstruction.IC);
					//printf("ID: currentInstruction.rs: %d  currentInstruction.rt: %d\n",currentInstruction.rs,currentInstruction.rt );

					/* if(currentInstruction.opcode == beq) { // if beq, raise up pending flag
						IF_ID_latch.branch = 1; // pending flag up
					} */

					// If instuctions in later latch are add sub or mul
					if((ID_EX_latch.instruction.opcode==add)||(ID_EX_latch.instruction.opcode==sub)||(ID_EX_latch.instruction.opcode==mul)) {
						if((currentInstruction.rs == ID_EX_latch.instruction.rd) || (currentInstruction.rt == ID_EX_latch.instruction.rd)) {
							hazard=1;
						}
					}
					if((EX_MEM_latch.instruction.opcode==add)||(EX_MEM_latch.instruction.opcode==sub)||(EX_MEM_latch.instruction.opcode==mul)) {
						if((currentInstruction.rs == EX_MEM_latch.instruction.rd) || (currentInstruction.rt == EX_MEM_latch.instruction.rd)) {
							hazard=1;
						}
					}
					if((MEM_WB_latch.instruction.opcode==add)||(MEM_WB_latch.instruction.opcode==sub)||(MEM_WB_latch.instruction.opcode==mul)) {
						if((currentInstruction.rs == MEM_WB_latch.instruction.rd) || (currentInstruction.rt == MEM_WB_latch.instruction.rd)) {
							hazard=1;
						}
					}

					if((ID_EX_latch.instruction.opcode==addi)||(ID_EX_latch.instruction.opcode==lw)) {
						if((currentInstruction.rs == ID_EX_latch.instruction.rt) || (currentInstruction.rt == ID_EX_latch.instruction.rt)) {
							hazard=1;
						}
					}
					if((EX_MEM_latch.instruction.opcode==addi)||(EX_MEM_latch.instruction.opcode==lw)) {
						if((currentInstruction.rs == EX_MEM_latch.instruction.rt) || (currentInstruction.rt == EX_MEM_latch.instruction.rt)) {
							hazard=1;
						}
					}
					if((MEM_WB_latch.instruction.opcode==addi)||(MEM_WB_latch.instruction.opcode==lw)) {
						if((currentInstruction.rs == MEM_WB_latch.instruction.rt) || (currentInstruction.rt == MEM_WB_latch.instruction.rt)) {
							hazard=1;
						}
					}
					//printf("ID: hazard=%d!!!!!!!!!!!!!!!!!!!!!1\n", hazard);
					if(hazard==0) {
						//printf("ID: no data hazard, doing add sub beq mul sw!   ");
						//printf("ID: work pc: %ld\n", currentInstruction.IC);
						ID_EX_latch.instruction=currentInstruction;//.opcode = IF_ID_latch.instruction.opcode;
						//ID_EX_latch.instruction.rs = IF_ID_latch.instruction.rs;
						//ID_EX_latch.instruction.rt = IF_ID_latch.instruction.rt;
						//ID_EX_latch.instruction.rd = IF_ID_latch.instruction.rd;
						// ID_EX_latch.instruction.Imm = IF_ID_latch.instruction.Imm; // pas Imm filed to the next
						// operating in ID Stage
						// ID_EX_latch.instruction.rd = IF_ID_latch.instruction.rd;
						ID_EX_latch.SourceVal1 = mips_reg[currentInstruction.rs];
						ID_EX_latch.SourceVal2 = mips_reg[currentInstruction.rt];
						ID_cycle_counter++;
						ID_cycle++;
						IF_ID_latch.free = 1;
						IF_ID_latch.valid = 0; // we read this instruction
						/* if((ID_EX_latch.prevFree == 1)&&(IF_ID_latch.free)){
						  ID_EX_latch.valid = 1; // ID_EX latch hasn't been read
						} */
					}
				}

				if((currentInstruction.opcode == addi) || (currentInstruction.opcode == lw)) {
					//printf("ID: current is addi or lw!   ");
					//	//printf("ID: new work pc: %ld\n", currentInstruction.IC);
					//printf("ID: currentInstruction.rs: %d \n",currentInstruction.rs );
					// If instuctions in later latch are add sub or mul
////printf("ID_EX_latch.opcode: %d, EX_MEM_latch.opcode: %d, MEM_WB_latch.opcode:%d\n",ID_EX_latch.instruction.opcode,ID_EX_latch.instruction.opcode,MEM_WB_latch.instruction.opcode);

					if((ID_EX_latch.instruction.opcode==add)||(ID_EX_latch.instruction.opcode==sub)||(ID_EX_latch.instruction.opcode==mul)) {
						if(currentInstruction.rs == ID_EX_latch.instruction.rd) {
							hazard = 1;
						}
					}
					if((EX_MEM_latch.instruction.opcode==add)||(EX_MEM_latch.instruction.opcode==sub)||(EX_MEM_latch.instruction.opcode==mul)) {
						if(currentInstruction.rs == EX_MEM_latch.instruction.rd) {
							hazard = 1;
						}
					}
					if((MEM_WB_latch.instruction.opcode==add)||(MEM_WB_latch.instruction.opcode==sub)||(MEM_WB_latch.instruction.opcode==mul)) {
						if(currentInstruction.rs == MEM_WB_latch.instruction.rd) {
							hazard = 1;
						}
					}
					if((ID_EX_latch.instruction.opcode==lw)||(ID_EX_latch.instruction.opcode==addi) ) {
						if(currentInstruction.rs == ID_EX_latch.instruction.rt) {
							hazard = 1;
						}
					}
					if((EX_MEM_latch.instruction.opcode==lw)||(EX_MEM_latch.instruction.opcode==addi) ) {
						if(currentInstruction.rs == EX_MEM_latch.instruction.rt) {
							hazard = 1;
						}
					}
					if((MEM_WB_latch.instruction.opcode==lw)||(MEM_WB_latch.instruction.opcode==addi) ) {
						if(currentInstruction.rs == MEM_WB_latch.instruction.rt) {
							hazard = 1;
						}
					}
					//printf("ID: hazard=%d!!!!!!!!!!!\n", hazard);

					if(hazard==0) {
						////printf("ID: check after instruction lalalala!\n");
						////printf("ID: currentInstruction.rs: %d \n",currentInstruction.rs );
						////printf("ID: currentInstruction.rs=%d\n",ID: currentInstruction.rs);
						////printf("     currentInstruction:\n");
						//printInstruction(currentInstruction);
						////printf("     ID_EX_latch.instruction:\n");
						//printInstruction(ID_EX_latch.instruction);
						////printf("     EX_MEM_latch.instruction:\n");
						//printInstruction(EX_MEM_latch.instruction);
						////printf("     MEM_WB_latch.instruction:\n");
						//printInstruction(MEM_WB_latch.instruction);

						//printf("ID: no data hazard, doing addi or lw!  ");
						//printf("ID: new work pc: %ld\n", currentInstruction.IC);
						//hazard=0;
						ID_EX_latch.instruction=currentInstruction;
						//printf("ID_EX_latch.instruction.opcode= %d\n",ID_EX_latch.instruction.opcode);
						// ID_EX_latch.instruction.Imm = IF_ID_latch.instruction.Imm;
						ID_cycle++;
						IF_ID_latch.free = 1;
						ID_cycle_counter++;
						IF_ID_latch.valid = 0;
						ID_EX_latch.SourceVal1=mips_reg[currentInstruction.rs];

					}
				}


			} else {
				ID_EX_latch.instruction=IF_ID_latch.instruction;
				ID_cycle_counter=1;
				ID_end=1;
				//printf("ID: meet halt!!!!!!!!!!!!!!!!!!!!!!!\n");
				ID_EX_latch.valid = 1;
			}
		} // the end of ID working stage
		//printf("ID: ID_EX_latch.pass: %d\n", ID_EX_latch.pass);
		//printf("ID_EX_latch.free: %d, ID_cycle_counter: %ld\n ", ID_EX_latch.free,ID_cycle_counter );


		if((ID_EX_latch.free == 1)&&(ID_cycle_counter==1)) {
			//printf("ID:about doing new work\n");
			ID_EX_latch.valid = 1; // ID_EX latch hasn't been read
			ID_cycle_counter=0;
			IF_ID_latch.pass=1;
		}
	} // the end of not the last instruction
	else {
		ID_EX_latch.valid = 1; // ID_EX latch hasn't been read
	}
	//printf("IF_ID_latch.free: %d\n", IF_ID_latch.free );
	//printf("ID: hazard=%d\n", hazard);
}// the end of ID Stage case


void EX(int m,int n, struct inst* IMEM) {
	assert(m>0);
	assert(n>0);
//printf("EX: EX_end=%d\n", EX_end);
	if(!EX_end) { //IMEM[pgm_c].opcode!=haltSimulation){// make it is not the last instruction
		static long EX_cycle_counter=0;
		total_EX_cycle++;
		static int EXOpcode;
		static struct inst EXInstruction;
		//printf("ID_EX_latch.valid : %d  , EX_MEM_latch.prevPass: %d, ID_EX_latch.pass==1: %d\n ",ID_EX_latch.valid, EX_MEM_latch.prevPass,ID_EX_latch.pass  );
		if((ID_EX_latch.valid == 1) && ((EX_MEM_latch.prevPass == 1)||(ID_EX_latch.free==0)||(ID_EX_latch.pass==1))) { // if the later latch hasn't finished the job, ex wait till it's done and add total cycle
			if(EX_cycle_counter==0) {
				EXInstruction=ID_EX_latch.instruction;
			}
			//printf("EX: doing  work  pc:%ld\n", EXInstruction.IC);
			ID_EX_latch.pass=0;
			if(EXInstruction.opcode!=haltSimulation) {
				EX_cycle++;


				ID_EX_latch.free = 0;
				EX_cycle_counter++;
				//printf("EX:EX_cycle_counter:%ld\n ",EX_cycle_counter );
				if(EX_cycle_counter == 1) {
					//printf("EX: start  new work  pc:%ld\n", ID_EX_latch.instruction.IC);
					EXOpcode=ID_EX_latch.instruction.opcode;


					EX_MEM_latch.instruction=ID_EX_latch.instruction;
					ID_EX_latch.instruction=initInst(ID_EX_latch.instruction);
					//printf("EX: ID_EX_latch.instruction.opcode=%d\n",ID_EX_latch.instruction.opcode);
					if(EX_MEM_latch.instruction.opcode == add) { // add

						//	assert(ID_EX_latch.SourceVal1!= NULL);
						//assert(ID_EX_latch.SourceVal2!=NULL);

						EX_MEM_latch.ResutVal = ID_EX_latch.SourceVal1 + ID_EX_latch.SourceVal2;
						//printf("meet add!!!!!!!!!    EX_MEM_latch.ResutVal=%ld\n   ",EX_MEM_latch.ResutVal);

					}

					if(EX_MEM_latch.instruction.opcode == sub) { // sub

						//		assert(ID_EX_latch.SourceVal1!= NULL);
						//	assert(ID_EX_latch.SourceVal2!=NULL);

						EX_MEM_latch.ResutVal = ID_EX_latch.SourceVal1 - ID_EX_latch.SourceVal2;

					}

					if(EX_MEM_latch.instruction.opcode == mul) { // mul

						//assert(ID_EX_latch.SourceVal1!= NULL);
						//assert(ID_EX_latch.SourceVal2!=NULL);

						EX_MEM_latch.ResutVal = ID_EX_latch.SourceVal1 * ID_EX_latch.SourceVal2;

					}

					if(EX_MEM_latch.instruction.opcode == addi) { // addi

						//assert(ID_EX_latch.SourceVal1!= NULL);
						//assert(ID_EX_latch.instruction.Imm!= NULL);

						EX_MEM_latch.SourceVal2 = ID_EX_latch.SourceVal1 + EX_MEM_latch.instruction.Imm; //r[t] = r[s] + IMM
						//printf("EX: meet addi@@@@@@@@@@@@@@@@@@@EX_MEM_latch.SourceVal2=%ld\n",EX_MEM_latch.SourceVal2 );

					}

					if(EX_MEM_latch.instruction.opcode == lw) { // load word

						//assert(ID_EX_latch.SourceVal1!= NULL);
						//assert(ID_EX_latch.instruction.Imm!= NULL);
						//printf(" EX_MEM_latch.instruction.Imm =%d  ID_EX_latch.SourceVal1=%ld\n   ",EX_MEM_latch.instruction.Imm, ID_EX_latch.SourceVal1);
						EX_MEM_latch.ResutVal = EX_MEM_latch.instruction.Imm + ID_EX_latch.SourceVal1; // need to put this in register, Rt = MEM[ResutVal]
						assert(EX_MEM_latch.ResutVal>=0);

					}

					if(EX_MEM_latch.instruction.opcode == sw) { // store word

						//assert(ID_EX_latch.SourceVal1!= NULL);
						//assert(ID_EX_latch.SourceVal2!= NULL);
						//assert(ID_EX_latch.instruction.Imm!= NULL);

						/*VERY IMPORTANT, PLEASE READ WHILE IMPLEMENT MEM and WB*/
						EX_MEM_latch.ResutVal = ID_EX_latch.SourceVal1 + EX_MEM_latch.instruction.Imm; //Here, ResutVal store where to manipulate data
						EX_MEM_latch.SourceVal2 = ID_EX_latch.SourceVal2;// this is the value to be put in MEM[ResutVal]
						assert(EX_MEM_latch.ResutVal>=0);

					}

					if(EX_MEM_latch.instruction.opcode == beq) { // branc on eqc
						//EX_MEM_latch.instruction.Imm = ID_EX_latch.instruction.Imm;
						IF_ID_latch.branch = 0;
						if(ID_EX_latch.SourceVal1 == ID_EX_latch.SourceVal2) {

							pgm_c = pgm_c + EX_MEM_latch.instruction.Imm;
							assert(pgm_c>=0);
						}
					}

				}// pass in the first cycle

				if(EXOpcode == mul) {
					if(EX_cycle_counter == m) {
						ID_EX_latch.free = 1;
						ID_EX_latch.valid = 0; // read ID_EX
						//printf("EX finishing new work!\n");
					}
				} else {
					if(EX_cycle_counter == n) {
						ID_EX_latch.free = 1;
						ID_EX_latch.valid = 0; // read ID_EX
						//printf("EX finishing new work!\n");
					}
				}
			} else {
				EX_end=1;

				//printf("EX: meet halt!!!!!!!!!!!!!!!!!!!!!!!\n");
				EX_MEM_latch.instruction=ID_EX_latch.instruction;
				EX_MEM_latch.valid = 1;
			}

		}
		if(EXOpcode==mul) {
			if((EX_MEM_latch.free == 1)&&(EX_cycle_counter==m)) {
				EX_MEM_latch.valid = 1; // ID_EX latch hasn't been read
				EX_cycle_counter=0;
				ID_EX_latch.pass=1;
				//printf("EX: about to pass work to MEM\n");
			}
		} else {
			if(EXOpcode==haltSimulation) {
				if((EX_MEM_latch.free == 1)&&(EX_cycle_counter==-1)) {
					EX_MEM_latch.valid = 1; // ID_EX latch hasn't been read
					EX_cycle_counter=0;
					ID_EX_latch.pass=1;
					//printf("EX: about to pass work to MEM\n");
				}
			} else {
				if((EX_MEM_latch.free == 1)&&(EX_cycle_counter==n)) {
					EX_MEM_latch.valid = 1; // ID_EX latch hasn't been read
					EX_cycle_counter=0;
					ID_EX_latch.pass=1;
					//printf("EX: about to pass work to MEM\n");
				}
			}
		}
	} else {
		EX_MEM_latch.valid = 1;
	}
}
void MEM(long* DMEM,int c) { //,struct inst* IMEM) { //,long temp_MEM) {
	assert(c>0);
	//printf("MEM:MEM_end=%d\n", MEM_end);
	if(!MEM_end) { //IMEM[pgm_c].opcode!=haltSimulation) {
		static long MEM_cycle_counter=0;
		static struct inst MEMInstruction;
		total_MEM_cycle++;
		//printf("MEM: EX_MEM_latch.valid: %d ,MEM_WB_latch.prevPass:%d, EX_MEM_latch.free: %d, EX_MEM_latch.pass: %d\n",EX_MEM_latch.valid,MEM_WB_latch.prevPass,EX_MEM_latch.free,EX_MEM_latch.pass );
		if((EX_MEM_latch.valid)&&((MEM_WB_latch.prevPass)||(EX_MEM_latch.free==0)||(EX_MEM_latch.pass==1))) {
			//printf("MEM: doing work\n");//, EX_MEM_latch.instruction.IC);
			if(MEM_cycle_counter==0) {
				MEMInstruction=EX_MEM_latch.instruction;
				MEM_WB_latch.ResutVal=EX_MEM_latch.ResutVal;
				MEM_WB_latch.SourceVal1=EX_MEM_latch.SourceVal1;
				MEM_WB_latch.SourceVal2=EX_MEM_latch.SourceVal2;

				//printf("Result pass from MEM to WB!!!! MEM_WB_latch.SourceVal2=%ld\n ", MEM_WB_latch.SourceVal2);

				//long SourceVal1; // value of rs

			}
			EX_MEM_latch.pass=0;
			if(MEMInstruction.opcode!=haltSimulation) {
				EX_MEM_latch.free=0;
				if(MEM_cycle_counter==0) {
					if(EX_MEM_latch.instruction.opcode==lw||EX_MEM_latch.instruction.opcode==sw) {
						if(((EX_MEM_latch.ResutVal)%4)!=0) {					//adress is deivided by 4

							//printf("A misaligned memory access occurs.\n");
							exit(0);
						}
					}
				}

				MEM_cycle_counter++;
				if(MEM_cycle_counter==1) {
					//printf("MEM: start new work  PC: %ld\n", EX_MEM_latch.instruction.IC);
					MEM_WB_latch.instruction=EX_MEM_latch.instruction;

					MEM_WB_latch.ResutVal=EX_MEM_latch.ResutVal;
					if(EX_MEM_latch.instruction.opcode==sw) { //if the instruction is sw
						EX_MEM_latch.ResutVal=EX_MEM_latch.ResutVal/4;
						DMEM[EX_MEM_latch.ResutVal]=EX_MEM_latch.SourceVal2;
					} else if(MEM_WB_latch.instruction.opcode==lw) {
						EX_MEM_latch.ResutVal=EX_MEM_latch.ResutVal/4;
						temp_MEM=DMEM[EX_MEM_latch.SourceVal2];
					}
					EX_MEM_latch.instruction=initInst(EX_MEM_latch.instruction);
				}
				if(MEM_cycle_counter==c) {
					//printf("MEM: finishing work!");
					EX_MEM_latch.free=1;
					MEM_cycle +=c;   //useful cycle of stage
					EX_MEM_latch.valid=0;
				}


			} else {
				MEM_cycle_counter=c;
				MEM_end=1;
				//printf("MEM: meet halt!!!!!!!!!!!!!!!!!!!!!!!\n");
				MEM_WB_latch.instruction=EX_MEM_latch.instruction;
				MEM_WB_latch.valid=1;
			}
		}
		if((MEM_WB_latch.free)&&(MEM_cycle_counter==c)) {
			EX_MEM_latch.pass=1;
			MEM_WB_latch.valid=1;
			MEM_cycle_counter=0;

		}
	} else {
		MEM_WB_latch.valid=1;
	}
	//printf("MEM: EX_MEM_latch.pass: %d  EX_MEM_latch.free: %d \n",EX_MEM_latch.pass,EX_MEM_latch.free);
}

void WB(long* mips_reg,struct inst* IMEM) { //,int flagofEnd ) {//long temp_MEM,
	//if(IMEM[pgm_c].opcode != haltSimulation) {
	static long WB_cycle_counter=0;
	total_WB_cycle++;
	if(MEM_WB_latch.valid) {
		//printf("WB: doing new work, PC: %ld\n", MEM_WB_latch.instruction.IC);
		if(MEM_WB_latch.instruction.opcode!=haltSimulation) {

			MEM_WB_latch.free=1;
			WB_cycle_counter++;
			//if(WB_cycle_counter==1) {
			// is R type

			if(MEM_WB_latch.instruction.opcode==add||MEM_WB_latch.instruction.opcode==sub||MEM_WB_latch.instruction.opcode==mul) {

				mips_reg[MEM_WB_latch.instruction.rd]=MEM_WB_latch.ResutVal;



			}
			// is I type
			else if (MEM_WB_latch.instruction.opcode==addi) { //||MEM_WB_latch.instruction.opcode==beq) {
				//printf("current is addi\n");
				//printf("MEM_WB_latch.instruction.rt: %d   MEM_WB_latch.SourceVal2: %ld\n",MEM_WB_latch.instruction.rt,MEM_WB_latch.SourceVal2);
				mips_reg[MEM_WB_latch.instruction.rt]=MEM_WB_latch.SourceVal2;

			}
			// is lw
			else {
				if(MEM_WB_latch.instruction.opcode==lw)
					mips_reg[MEM_WB_latch.instruction.rt]=temp_MEM;

			}
			MEM_WB_latch.instruction=initInst(MEM_WB_latch.instruction);
			//}
			//if(WB_cycle_counter==1) {
			MEM_WB_latch.free=1;
			WB_cycle_counter=0;
			WB_cycle +=1;           //useful cycle
			MEM_WB_latch.valid=0;
			//}
		} else {

			flagofEnd=1;
			//printf("WB: meet halt!!!!!!!!!!!!!!!!!!!!!!!\n");
		}
	}

}
/*********************************************************/
struct inst parser() { //char *instStr) { //, long *mips_reg){
	////printf("enter!\n");
	int i;
	char delimiters[]=" ";
	char ** instructionFields;
////printf("enter!\n");
	instructionFields = (char **)malloc(4*sizeof(char *));
	for (i=0; i<4; i++)
		*(instructionFields+i) = (char *) malloc(20*sizeof(char *));
	////printf("enter!\n");
	////printf("%s\n",instStr);
	char instSt[100];
	strcpy(instSt, instrc);
	instructionFields[0] = strtok(instSt, delimiters);
	////printf("%s\n",instructionFields[0]);
	instructionFields[1] = strtok(NULL, delimiters);
	instructionFields[2] = strtok(NULL, delimiters);
	instructionFields[3] = strtok(NULL, delimiters);
	////printf("%s\n%s\n%s \n%s\n",instructionFields[0],instructionFields[1],instructionFields[2] ,instructionFields[3]  );
	struct inst instruction;
	instruction.IC=pgm_c;
	//instruction.opcode=(opcodeEnum)instructionFields[0];
	int opcodefromInput;

	if(!strcmp(instructionFields[0],"add")) {
		opcodefromInput=0;
	} else {
		if(!strcmp(instructionFields[0],"addi")) {
			opcodefromInput=1;
		} else {
			if(!strcmp(instructionFields[0],"sub")) {
				opcodefromInput=2;
			} else {
				if(!strcmp(instructionFields[0],"mul")) {
					opcodefromInput=3;
				} else {
					if(!strcmp(instructionFields[0],"beq")) {
						opcodefromInput=4;
					} else {
						if(!strcmp(instructionFields[0],"lw")) {
							opcodefromInput=5;
						} else {
							if(!strcmp(instructionFields[0],"sw")) {
								opcodefromInput=6;
							} else {
								if(!strcmp(instructionFields[0],"haltSimulation")) {
									opcodefromInput=7;
								} else {
									printf("Illegal opcode\n");
									exit(0);
								}
							}
						}
					}
				}
			}
		}
	}


	switch(opcodefromInput) {
	//add rd rs rt
	case add :
		////printf("enteradd\n");
		instruction.opcode=add;
		if((*instructionFields[2])!='$') {
			printf("Missing $ in front of a register name\n");
			exit(0);
		} else instruction.rs=atoi(instructionFields[2]+1);

		if((*instructionFields[3])!='$') {
			printf("Missing $ in front of a register name\n");
			exit(0);
		} else instruction.rt=atoi((instructionFields[3]+1));


		if((*instructionFields[1])!='$') {
			printf("Missing $ in front of a register name\n");
			exit(0);
		} else instruction.rd=atoi(instructionFields[1]+1);

		break;
	//addi $rt, $rs, immed
	case addi :
		instruction.opcode=addi;
		if((*instructionFields[2])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rs=atoi(instructionFields[2]+1);

		if((*instructionFields[1])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rt=atoi(instructionFields[1]+1);

		instruction.Imm=atoi(instructionFields[3]);
		//printf("imm: %d\n %f\n", instruction.Imm, pow(2,15));
		if((instruction.Imm>(pow(2,15)-1)) || (instruction.Imm<(-pow(2,15)))) {
			printf("Immediate field that contains a number too large to store in the 16 bits that are available in the machine code format.\n");
			exit(0);
		}

		break;

	//sub rd rs rt
	case sub :
		instruction.opcode=sub;
		if((*instructionFields[2])!='$') {
			printf("Missing $ in front of a register name\n");
			exit(0);
		} else instruction.rs=atoi(instructionFields[2]+1);

		if((*instructionFields[3])!='$') {
			printf("Missing $ in front of a register name\n");
			exit(0);
		} else instruction.rt=atoi(instructionFields[3]+1);


		if((*instructionFields[1])!='$') {
			printf("Missing $ in front of a register name\n");
			exit(0);
		} else instruction.rd=atoi(instructionFields[1]+1);

		break;

	//mul rd rs rt
	case mul :
		instruction.opcode=mul;
		if((*instructionFields[1])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rd=atoi(instructionFields[1]+1);

		if((*instructionFields[2])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rs=atoi(instructionFields[2]+1);

		if((*instructionFields[3])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rt=atoi(instructionFields[3]+1);

		break;


	//beq rs rt immed
	case beq :
		instruction.opcode=beq;
		if((*instructionFields[2])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rt=atoi(instructionFields[2]+1);

		if((*instructionFields[1])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rs=atoi(instructionFields[1]+1);

		instruction.Imm=atoi(instructionFields[3]);
		if((instruction.Imm>(pow(2,15)-1)) || (instruction.Imm<(-pow(2,15)))) {
			printf("Immediate field that contains a number too large to store in the 16 bits that are available in the machine code format.\n");
			exit(0);
		}
		break;

	//lw rt immed rs
	case lw :
		instruction.opcode=lw;
		instruction.Imm=atoi(instructionFields[2]);
		if((instruction.Imm>(pow(2,15)-1)) || (instruction.Imm<(-pow(2,15)))) {
			printf("Immediate field that contains a number too large to store in the 16 bits that are available in the machine code format.\n");
			exit(0);
		}
		if((*instructionFields[1])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rt=atoi(instructionFields[1]+1);

		if((*instructionFields[3])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rs=atoi(instructionFields[3]+1);

		break;
	//sw rt immed rs
	case sw :
		instruction.opcode=sw;
		instruction.Imm=atoi(instructionFields[2]);
		if((instruction.Imm>(pow(2,15)-1)) || (instruction.Imm<(-pow(2,15)))) {
			printf("Immediate field that contains a number too large to store in the 16 bits that are available in the machine code format.\n");
			exit(0);
		}
		if((*instructionFields[1])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rt=atoi(instructionFields[1]+1);

		if((*instructionFields[3])!='$') {
			printf("Missing $ in front of a register name.\n");
			exit(0);
		} else instruction.rs=atoi(instructionFields[3]+1);

		/* if((instruction.Imm+mips_reg[instruction.rs])%4!=0){
			printf("Misaligned memory access occurs.");
			exit(0);
		} */

		break;

	case haltSimulation:
		instruction.opcode=haltSimulation;

	}
	//printf("op:%d rd:%d rs:%d rt:%d  imm:%d\n",instruction.opcode, instruction.rd,instruction.rs,instruction.rt,instruction.Imm );
	//IM[PC]=instruction;
	return instruction;
}
/* Converter.c***********************************************/
void regNumberConverter(char* preScan) {
	//printf("input of converter: @%s@\n",preScan);
	char* RegVal[32] = {"$zero", "$at", "$v0", "$v1", "$a0", "$a1", "$a2", "$a3", "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$s0", "$s1",
	                    "$s2", "$s3", "$s4", "$s5", "$s6", "$s7", "$t8", "$t9", "$k0", "$k1", "$gp", "$sp", "$fp", "$ra"
	                   };
	enum Reg {$zero, $at, $v0, $v1, $a0, $a1, $a2, $a3, $t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7, $s0, $s1, $s2, $s3, $s4,
	          $s5, $s6, $s7, $t8, $t9, $k0, $k1, $gp, $sp, $fp, $ra
	         };
	char* RegNum[32] = {"$0", "$1", "$2", "$3", "$4", "$5", "$6", "$7", "$8", "$9", "$10", "$11", "$12", "$13", "$14", "$15", "$16", "$17",
	                    "$18", "$19", "$20", "$21", "$22", "$23", "$24", "$25", "$26", "$27", "$28", "$29", "$30", "$31"
	                   };
	enum Reg num;
	char line[80];
	int count;
	char str[40];
	instrc[0]='\0';
	int i;
//char instrc[40];
	strcpy(line, preScan);
	char* subString;
	char sign[]="$";
//  char temp[40]="$";
	subString=strtok(line, " ");               //token the command
	memset(str, '\0', sizeof(str));
//memset(instrc, '\0', sizeof(instrc));
//  printf("str: %s\n",str);
	while(subString != NULL) {
		if(subString[0]=='$') {
			for(i=0; i<32; i++) {
				if(!strcmp(subString,RegVal[i])||!strcmp(subString,RegNum[i])) {
					num=i;
					strcat(instrc,sign);
					sprintf(str,"%d", num);           //change the int to string
					break;
				} else {
					if(i==31) {
						printf("illegal register name is detected\n");
						exit(0);
					}
				}
			}
		}
		if(subString[0]!='$') {             //not a register
			strcpy(str,subString);
		}
		subString[0]='\0';
		subString=strtok(NULL, " ");             //token field of a instruction
//printf("subString: @%s@\n",subString);
		strcat(instrc,strcat(str," "));
	}
	//printf("output of converter: @%s@\n",instrc);
}

/*proScanner**************************************************/

char *progScanner(char* scanedChar) {
	int i,j,k; // loop counter
	bool closeParentFlag;// check if the Parentheses closed
	char *modStr; // chunck of string without any prantethis, comma, or spaces
	char *combArr = malloc(200*sizeof(char)); // combine these strings with a Parentheses one after
	char *space;//

	for(i = 0; scanedChar[i] != '\0'; i++) { // we're trying to simiplify the problem by changing special char in to space
		//Later on, we will deal with spaces with delimiters

		// Make Sure that char to lower case
		//scanedChar[i] = tolower(scanedChar[i]);

		//Get rid of the commas
		if(scanedChar[i] == ',') {
			scanedChar[i] = ' ';
		}

		// Deal with prantethis duplicate or doesn't close
		if(scanedChar[i] == '(') {
			closeParentFlag = false; // initiate the close prantethis flag

			for(j = i+1; scanedChar[j] != '\0'; j++) {
				if(scanedChar[j] == '(') { // if there is any left Parentheses after one
					perror("Error with prantethis duplicate");
					exit(0);

				} else if(scanedChar[j] == ')') {
					closeParentFlag = true; // if there is a close Parentheses after left, flag is to true
				}
			}

			if(closeParentFlag == false) { // if the close parenthes flag is not on, instruction doesn't close parenthes
				perror("Error with prantethis close");
				exit(0);
			}

			scanedChar[i] = ' ';
		}// close the if to deal with all Parentheses

		// Deal with one single close prantethis
		if(scanedChar[i] == ')') {
			scanedChar[i] = ' ';
		}
	} // close the for loop for dealing with , and prantethis

	//Now, we need to get rid of all duplicated spaces
	modStr = strtok(scanedChar, " "); // take the first token from original string
	space = " ";// give space a value, we're going to insert this value right behind each token except for the last one
	k = 0;// countr start from 0, this counter will tell us wether we're reaching the end of the instruction, avoid inserting 0

	while(modStr != NULL) { // we will split based on ' ' in modStr and recombine the tokens together in combArr

		strcat(combArr, modStr); // put first, second,....token into the combArr
		k++;
		if(k < 4) { // more sure we don't accidentally insert a space after the last part of the instruction
			strcat(combArr, space); // put a space behind the new combined
		}

		modStr = strtok(NULL, " "); // update modStr

	}// close while loop
	return combArr;
}


//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

int main(int argc, char *argv[]) {
	int sim_mode=0;//mode flag, 1 for single-cycle, 0 for batch
	int c,m,n;
	int i;//for loop counter
	long mips_reg[REG_NUM];
	//long pgm_c=0;//program counter
	long sim_cycle=0;//simulation cycle counter
	int test_counter=0;//!!!!!!!!!!!what is this for??????????????
	FILE *input=NULL;
	FILE *output=NULL;

	printf("The arguments are:");

	for(i=1; i<argc; i++) {
		printf("%s ",argv[i]);
	}
	printf("\n");
	if(argc==7) {
		if(strcmp("-s",argv[1])==0) {
			sim_mode=SINGLE;
		} else if(strcmp("-b",argv[1])==0) {
			sim_mode=BATCH;
		} else {
			printf("Wrong sim mode chosen\n");
			exit(0);
		}

		m=atoi(argv[2]);
		n=atoi(argv[3]);
		c=atoi(argv[4]);
		input=fopen(argv[5],"r");
		output=fopen(argv[6],"w");

	}

	else {
		printf("Usage: ./sim-mips -s m n c input_name output_name (single-sysle mode)\n or \n ./sim-mips -b m n c input_name  output_name(batch mode)\n");
		printf("m,n,c stand for number of cycles needed by multiplication, other operation, and memory access, respectively\n");
		exit(0);
	}
	if(input==NULL) {
		printf("Unable to open input or output file\n");
		exit(0);
	}
	if(output==NULL) {
		printf("Cannot create output file\n");
		exit(0);
	}
	//initialize registers and program counter!!!!!Why????????????????
	//if(sim_mode==1){
	for (i=0; i<REG_NUM; i++) {
		mips_reg[i]=0;
	}
	//}
	//start your code from here


	//IMEM and DMEM
	struct inst IMEM[512];
	long DMEM[512];
	IF_ID_latch.instruction=initInst(IF_ID_latch.instruction);
	ID_EX_latch.instruction=initInst(ID_EX_latch.instruction);
	EX_MEM_latch.instruction=initInst(EX_MEM_latch.instruction);
	MEM_WB_latch.instruction=initInst(MEM_WB_latch.instruction);
	PC_latch.instruction=initInst(PC_latch.instruction);

	//initialize latches
	//at the beginning all stages are availble
	IF_ID_latch.free=1;
	ID_EX_latch.free=1;
	EX_MEM_latch.free=1;
	MEM_WB_latch.free=1;
	PC_latch.free=1;
	IF_ID_latch.pass=1;
	ID_EX_latch.pass=1;
	EX_MEM_latch.pass=1;
	MEM_WB_latch.pass=1;
	PC_latch.pass=1;
	IF_ID_latch.prevPass=1;
	ID_EX_latch.prevPass=1;
	EX_MEM_latch.prevPass=1;
	MEM_WB_latch.prevPass=1;
	PC_latch.prevPass=1;

	IF_ID_latch.valid = 0;
	ID_EX_latch.valid = 0;
	EX_MEM_latch.valid = 0;
	MEM_WB_latch.valid = 0;


	PC_latch.branch=0;
	PC_latch.prevBranch=0;
	//load instructions from the file to the IMEM
	char currentInst[100];
	char *refinedInst;
	char *InstWithRegNum;
	printf("start!\n");



	while(fgets(currentInst, 100, input)!=NULL) {
		if(strcmp(currentInst,"haltSimulation"))
			currentInst[strlen(currentInst)-1]='\0';
		printf("read string: @%s@\n",currentInst);
		refinedInst=progScanner(currentInst);
		regNumberConverter(refinedInst);//!!!!!??????!!!!!!!!!!!!!!!!!
		//printf("converter output in main: @%s@\n", instrc);
		instrc[strlen(instrc)-1]='\0';
		//printf("converter output in main: @%s@\n", instrc);
		IMEM[pgm_c]=parser();
		//printf("Already in the IMEM: op:%d rd:%d rs:%d rt:%d  imm:%d PC: %ld\n\n",IMEM[pgm_c].opcode, IMEM[pgm_c].rd,IMEM[pgm_c].rs,IMEM[pgm_c].rt,IMEM[pgm_c].Imm,IMEM[pgm_c].IC  );
		pgm_c++;
		//fgets(currentInst, 100, input);

	}//instructions are all loaded into IMEM!!!

//exit(0);
	//start operating MIPS!!!!!!!!!!
	pgm_c=0;
	//move=1;
	while(flagofEnd != 1) {
		WB(mips_reg,IMEM);//);//temp_MEM,
		MEM( DMEM, c);//,IMEM);//,temp_MEM);
		EX(m,n, IMEM);
		//EX_MEM_latch.prevFree = EX_MEM_latch.free;
		EX_MEM_latch.prevPass=EX_MEM_latch.pass;
		ID(IMEM,mips_reg );
		//ID_EX_latch.prevFree = ID_EX_latch.free;
		ID_EX_latch.prevPass=ID_EX_latch.pass;
		IF(IMEM,c);
		IF_ID_latch.prevPass=IF_ID_latch.pass;
		//IF_ID_latch.prevFree= IF_ID_latch.free;
		PC_latch.prevBranch=PC_latch.branch;
		sim_cycle+=1;
		//sim_cycle++;
		//////////////////////////////////////////////////////////////
		//output code 2: the following code will output the register
		//value to screen at every cycle and wait for the ENTER key
		//to be pressed; this will make it proceed to the next cycle
		//output code 2: the following code will output the register
		//value to screen at every cycle and wait for the ENTER key
		//to be pressed; this will make it proceed to the next cycle

		if(sim_mode==1) {
			printf("cycle: %ld register value: ",sim_cycle);
			for (i=1; i<REG_NUM; i++) {
				printf("%ld  ",mips_reg[i]);
			}
			printf("program counter: %ld\n",pgm_c);
			printf("press ENTER to continue\n");
			while(getchar() != '\n');
		}

		//sim_cycle+=1;

		//	printf("cycle: %ld \n",sim_cycle);

		/* if(sim_mode==1) {
			for (i=1; i<REG_NUM; i++) {
				printf("register%d: %ld  \n ",i, mips_reg[i]);
			}
		} */
		//	printf("pgm_c:%ld\n",pgm_c);
		//pgm_c+=4;

		//test_counter++;
		//printf("press ENTER to continue\n");
		//while(getchar() != '\n');

	}//MIPS finished!!!!!!!!!!!!!!!!
	//total_IF_cycle=total_IF_cycle-1;
//	IF_cycle=ID_cycle-1;

	/* printf("IF_cycle=%ld     ",IF_cycle);
	printf("total_IF_cycle=%ld\n",total_IF_cycle);
	printf("ID_cycle=%ld    ",ID_cycle);printf("total_ID_cycle=%ld\n",total_ID_cycle);
	printf("EX_cycle=%ld    ",EX_cycle);printf("total_EX_cycle=%ld\n",EX_cycle);
	printf("MEM_cycle=%ld    ",MEM_cycle); printf("total_MEM_cycle=%ld\n",total_MEM_cycle);
	printf("WB_cycle=%ld     ",WB_cycle);
	printf("total_WB_cycle=%ld\n",total_WB_cycle); */



	double ifUtil=(double)IF_cycle/(double)(total_IF_cycle-1);
	double idUtil=(double)ID_cycle/(double)(total_ID_cycle-1);
	double exUtil=(double)EX_cycle/(double)(total_EX_cycle-1);
	double memUtil=(double)MEM_cycle/(double)(total_MEM_cycle-1);
	double wbUtil=(double)WB_cycle/(double)(total_WB_cycle-1);
	//add the following code to the end of the simulation,
	//to output statistics in batch mode
	if(sim_mode==0) {
		fprintf(output,"program name: %s\n",argv[5]);
		fprintf(output,"stage utilization: %f  %f  %f  %f  %f \n",
		        ifUtil, idUtil, exUtil, memUtil, wbUtil);
		// add the (double) stage_counter/sim_cycle for each
		// stage following sequence IF ID EX MEM WB

		fprintf(output,"register values ");
		for (i=1; i<REG_NUM; i++) {
			fprintf(output,"%ld  ",mips_reg[i]);
		}
		fprintf(output,"%ld\n",pgm_c);

	}
	//close input and output files at the end of the simulation
	fclose(input);
	fclose(output);
	return 0;
}
