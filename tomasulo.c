
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9


/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];   //EY->Shang: 0-9, 9 is latest insn, 0 is oldest insn, queue shifts whenever instruction is 
//number of instructions in the instruction queue
static int instr_queue_size = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];


/* ECE552 Assignment 3 - BEGIN CODE */

//the index of the last instruction fetched
static int fetch_index = 0;

// ECE552 Extra Helper Functions Used (see bottom of file for full code)
static bool ifq_not_full(void); //TODO: maybe change this to macro later
static int fu_not_busy(enum md_opcode op); //TODO: maybe change this to macro later
static void shift_ifq(); 
static int rs_not_full(enum md_opcode op);

// UNCOMMENT LINE BELOW TO ENABLE DEBUG MESSAGES
// #define DBG_VIEW

// ### DEBUGGER ###
#ifdef DBG_VIEW
static void DBG_viewCycleTable(instruction_trace_t* trace, int lastcycle);
static void DBG_viewCycle(int cycle);
static void DBG_viewIFQ_FUstatus(void);
static void DBG_viewRS(void);
static void DBG_viewMapTable_CDB(void);
#endif

/* FUNCTIONAL UNITS */
/* Tag | FU 		<-- functional unit status						
						
	0  | FU_INT_0
	1  | FU_INT_1
	2  | FU_FP_0	<-- FU offset
*/

/* RESERVATION STATIONS */
/* Tag | FU | busy | Op | reg_out[0..1] | reg_in[0..2] | v[0..2]*						
							*v[0..2] contains the reserved values
							
	0  | fuINT0		<-- reservation station for fuINTs
	1  | fuINT1
	2  | fuINT2
	3  | fuINT3
	4  | fuFP0		<-- reservation station for fuFP
	5  | fuFP1
*/

/* ECE552 Assignment 3 - END CODE */


/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: YOUR CODE GOES HERE */
  /* ECE552 Assignment 3 - BEGIN CODE */
  int i;

  if( sim_insn > 0 ){
	  // Check if the reservation station
	  // If it is empty => simulation done
	  for( i=0; i < RESERV_INT_SIZE; i++ ){
		  if( reservINT[i] != NULL ){
			  return false;
		  }
	  }
	  
	  for( i=0; i < RESERV_FP_SIZE; i++ ){
		  if( reservFP[i] != NULL ){
			  return false;
		  }
	  }
	  //Also need to check if CDB is NULL
	  if(commonDataBus!=NULL)
		return false;
	  
	  return true;
  }
  
  return false; 
 /* ECE552 Assignment 3 - END CODE */
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  /* ECE552 Assignment 3 - BEGIN CODE */

  int i, j;
  
  if(commonDataBus!=NULL)
	commonDataBus->tom_cdb_cycle = current_cycle;
  else
	return;
  
  // Broadcast the CDB to INT reservation station
  for( i=0; i < RESERV_INT_SIZE; i++ ) {
	  for( j=0; j < 3; j++ ) {
 		  if(reservINT[i]!=NULL){
		  	if( (reservINT[i]->Q[j] != NULL) && (reservINT[i]->Q[j] == commonDataBus) ) {
				  // we simply clear the dependency on the
				  // dest registers
				  reservINT[i]->Q[j] = NULL;
		  	}
		  }
	  }
  }
  // Broadcast the CDB to FP reservation station
  for( i=0; i < RESERV_FP_SIZE; i++ ){
	  for( j=0; j < 3; j++ ){
		  if(reservFP[i]!=NULL){
			  if( (reservFP[i]->Q[j] != NULL) && (reservFP[i]->Q[j] == commonDataBus) ) {
				  reservFP[i]->Q[j] = NULL;
			  }
		  }
	  }
  }
  
  commonDataBus = NULL;
  /* ECE552 Assignment 3 - END CODE */

}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  /* ECE552 Assignment 3 - BEGIN CODE */

  int i,j;
  int FU_oldest_tag = -1;
  int FU_oldest_index = -1;
  bool FU_oldest_isINT = true;
   
  /* #######################################################
     ##### WE COVER THE issue_To_execute IN THIS STAGE #####
     ####################################################### */

  // Execute each issued instr. in fuINT FUs.
  for( i=0; i < FU_INT_SIZE; i++ ) {
	  if( fuINT[i] != NULL ) {
		  
		  // Case 1 - the instr. just got into the FU and not yet been executed
		  if( fuINT[i]->tom_execute_cycle == 0 ) {
			  // Just go ahead and execute
			  fuINT[i]->tom_execute_cycle = current_cycle;
		  }
		  else if( !WRITES_CDB(fuINT[i]->op) ){
			  // This is a store which does not go into the CDB
			  // There is no contention with other instructions which write to CDB 
			  // so we can clear it's functional unit and
			  // reservation station if the store op is complete
			  if((current_cycle - FU_INT_LATENCY+1) == (fuINT[i]->tom_execute_cycle)){
			  	for( j=0; j < RESERV_INT_SIZE; j++ ){
					  if( reservINT[j] == fuINT[i] ) {
						  assert(reservINT[j] != NULL);
						  reservINT[j] = NULL;
					  }
				}
				fuINT[i] = NULL;
			  }
			  else{
				assert((current_cycle - FU_INT_LATENCY+1) < (fuINT[i]->tom_execute_cycle));
			  } 	
		  }
		  else if( (current_cycle - FU_INT_LATENCY+1) >= (fuINT[i]->tom_execute_cycle) ) {
			  // Case 2 - the instr. just finished executing
			  //		  and it uses intFU FU
			  //		  OR there are other instr. in the CDB queue and
			  //		  this instr. is not qualified for going into CDB
			  if( FU_oldest_tag == -1 ){
				  FU_oldest_tag = i;
				  FU_oldest_index = fuINT[i]->index;
			  }
			  else{
				  // We pick the oldest-qualified instr.
				  // and put it into the CDB queue
				  if( fuINT[i]->index < FU_oldest_index ){
					FU_oldest_tag = i;
					FU_oldest_index = fuINT[i]->index;
				  }
			  }
			  
		  }
		  else{
			  // Case 3 - the instr. is already in the execution stage
		  }
	  }
  }
  
  for( i=0; i < FU_FP_SIZE; i++ ){
	  
	  if( fuFP[i] != NULL ){
		  if( fuFP[i]->tom_execute_cycle == 0 ){
			  fuFP[i]->tom_execute_cycle = current_cycle;
		  }
		  else if(((current_cycle - FU_FP_LATENCY+1) >= (fuFP[i]->tom_execute_cycle)) ){
			// Case 3 - the instr. finished
			//		  and it uses fpFU FU
			if( FU_oldest_tag == -1 ){
				FU_oldest_tag = i;
				FU_oldest_index = fuFP[i]->index;
				FU_oldest_isINT = false;
			}
			else{
			    if( fuFP[i]->index < FU_oldest_index ){
					FU_oldest_tag = i;
					FU_oldest_index = fuFP[i]->index;
					FU_oldest_isINT = false;
				}
			}
		  }
	  }
  }
  
  // If non of the instructions are have completed
  // do nothing
  if( FU_oldest_tag == -1 ){
	  return;
  }
  //printf("Oldest FU index: %d, tag : %d, %s\n",FU_oldest_index, FU_oldest_tag, MD_OP_NAME(fuINT[FU_oldest_tag]->op));
  // We found the oldest-qualifying instr. that finished exection
  if( FU_oldest_isINT ){
	  // Copy data to CDB
	  commonDataBus = fuINT[FU_oldest_tag];
	  
	  // Clear map table
	  for( i=0; i < 2; i++ ){
		  if( fuINT[FU_oldest_tag]->r_out[i] != DNA){
			  if(map_table[ fuINT[FU_oldest_tag]->r_out[i]]!=NULL)
				  if(map_table[ fuINT[FU_oldest_tag]->r_out[i]]->index == FU_oldest_index)
					  map_table[ fuINT[FU_oldest_tag]->r_out[i] ] = NULL;
		  }
	  }
	  
	  // Clear reservation station for this instr.
	  for( i=0; i < RESERV_INT_SIZE; i++ ){
		  if( reservINT[i] == fuINT[FU_oldest_tag] ) {
			  reservINT[i] = NULL;
			  break;
		  }
	  }
	  assert(reservINT[i] == NULL);
	  
	  // Clear functional unit reservation for this instr.
	  fuINT[FU_oldest_tag] = NULL;
  }
  else{
	  // the finished instr. is a FP instr.
	  
	  commonDataBus = fuFP[FU_oldest_tag];
	  
	  for( i=0; i < 2; i++ ){
		  if( fuFP[FU_oldest_tag]->r_out[i] != DNA ){
			  if(map_table[ fuFP[FU_oldest_tag]->r_out[i]]!=NULL)
				  if(map_table[ fuFP[FU_oldest_tag]->r_out[i]]->index == FU_oldest_index)
					 map_table[ fuFP[FU_oldest_tag]->r_out[i] ] = NULL;
		  }
	  }
	  
	  // Clear reservation station for this instr.
	  for( i=0; i < RESERV_FP_SIZE; i++ ) {
		  if( reservFP[i] == fuFP[FU_oldest_tag] ) {
			  reservFP[i] = NULL;
			  break;
		  }
	  }
 	  assert(reservFP[i] == NULL);
  
	  // Clear functional unit reservation for this instr.
	  fuFP[FU_oldest_tag] = NULL;
  }
  /* ECE552 Assignment 3 - END CODE */
  
}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  /* ECE552 Assignment 3 - BEGIN CODE */

  int i;
  int RS_oldest_INTtag;
  int RS_oldest_FPtag;
  int RS_oldest_INTindex;	// temperary variable for finding the tag
  int RS_oldest_FPindex;
  //bool RS_oldest_isintFU = true; // determine if the qualified instr. for issue is a intFU or fpFU
  int RS_FU_allocate;
  
  // Way of issuing:
  //	1. we tried the oldest entry qualified for issue in RS
  // 	2. if FU is occupied at the moment we simply stall
  
  // Find the oldest instr. without RAW right after dispatch
  // since n=6 (i.e. 6 RS slots) is small we don't need to use
  // efficient sorting algorithm like quicksort in this case
  // just use the simple try-and-error approach
  

  while(fuINT[0]==NULL || fuINT[1] == NULL){//no fuINT available
	  RS_oldest_INTtag = -1;
	  RS_oldest_INTindex = -1;
	  RS_FU_allocate = -1;
	  for( i=0; i < RESERV_INT_SIZE; i++ ){
		// this part is inefficient as it repeats the rs_not_full for RESERV_INT_SIZE time
		if(( reservINT[i] != NULL) && (reservINT[i]->tom_issue_cycle == 0) ) {
			if( (reservINT[i]->Q[0] == NULL) && (reservINT[i]->Q[1] == NULL) && (reservINT[i]->Q[2] == NULL) ) {
				if( RS_oldest_INTtag != -1 ){
					if( reservINT[i]->index < RS_oldest_INTindex ){
						RS_oldest_INTtag = i;
						RS_oldest_INTindex = reservINT[i]->index;
					}
				}
				else{
					RS_oldest_INTtag = i;
					RS_oldest_INTindex = reservINT[i]->index;
				}
			}
		}
  	}
	if( RS_oldest_INTtag == -1 ) {
		  break;
	}
	else{
		  RS_FU_allocate = fu_not_busy(reservINT[RS_oldest_INTtag]->op);
		  fuINT[RS_FU_allocate] = reservINT[RS_oldest_INTtag];
		  // Update the issue cycle
		  reservINT[RS_oldest_INTtag]->tom_issue_cycle = current_cycle;
	}	
  }
  if(fuFP[0]==NULL){
	  RS_oldest_FPtag = -1;
          RS_oldest_FPindex = -1;
	  RS_FU_allocate = -1;
	  for( i=0; i < RESERV_FP_SIZE; i++ ){
		if(( reservFP[i] != NULL) && (reservFP[i]->tom_issue_cycle == 0) ) {
			if( (reservFP[i]->Q[0] == NULL) && (reservFP[i]->Q[1] == NULL) && (reservFP[i]->Q[2] == NULL) ){
				if( RS_oldest_FPtag != -1 ){
					if( reservFP[i]->index < RS_oldest_FPindex ){
						RS_oldest_FPtag = i;
						RS_oldest_FPindex = reservFP[i]->index;
					}
				}
				else{
					// first choice of RS_oldest_tag with the corresponding index
					RS_oldest_FPtag = i;
					RS_oldest_FPindex = reservFP[i]->index;
				}
			}
		}
  	}
	if( RS_oldest_FPtag == -1 ) {
		 return;
	}
	else{
		  RS_FU_allocate = fu_not_busy(reservFP[RS_oldest_FPtag]->op);
		  fuFP[RS_FU_allocate] = reservFP[RS_oldest_FPtag];
		  // Update the issue cycle
		  reservFP[RS_oldest_FPtag]->tom_issue_cycle = current_cycle;
	}	

  }

  return;
  /* ECE552 Assignment 3 - END CODE */

}


/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {

  int i;
  instruction_t* new_instr = NULL;

  /* ECE552: YOUR CODE GOES HERE */
  /* ECE552 Assignment 3 - BEGIN CODE */

  if( ifq_not_full() ){
	
	do{
		// the first instruction in the trace starts from index 1
		fetch_index++;
		new_instr = get_instr(trace, fetch_index);
		if(new_instr == NULL) return; // if instruction trace is complete, return
		if(new_instr->op == 0) return;

	}while( IS_TRAP( new_instr->op ) );
	
	// It is a non-trap instr. & ifq not full => we use this instr.
	
	// Initialize Q fields
	for( i=0; i < 3; i++ ){
		new_instr->Q[i] = NULL;
	}
	
	// Initialize cycle stats
	new_instr->tom_dispatch_cycle = 0;
	new_instr->tom_issue_cycle = 0;
	new_instr->tom_execute_cycle = 0;
	new_instr->tom_cdb_cycle = 0;

	//printf(" -------------------------- Current Op : %s -------------------------  \n\n", MD_OP_NAME(new_instr->op));
	//printf("Test: %s, %d\n", MD_OP_NAME((md_opcode)0x01),new_instr->op);
	instr_queue[instr_queue_size] = new_instr;
	instr_queue_size++;

	/* Instr. queue
		| 0 | -- oldest instr -- |	<-- always pick this to run
		| 1 |		..			 |
		| . |		..			 |
		| 9 | newly added instr  |	<-- new instr. added here
	*/
  }
  else{
	// IFQ is full so cannot fetch another instruction right now, return, do nothing, this should be a STALL 
	return;
  }
  /* ECE552 Assignment 3 - END CODE */
}

/* Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

  fetch(trace);

  /* ECE552: YOUR CODE GOES HERE */
  /* ECE552 Assignment 3 - BEGIN CODE */

  
  int i, j;
  int RS_tag = -1;
  int RS_RAW = 0;
  
  /* if there is an available reservation station, dispatch the most recent instruction from the IFQ
	 and set tom_dispatch_cycle to current_cycle for that instr.
	 also shift the elements of the IFQ so that the dispatched instruction is kicked out of the queue
     
	 "Treat them the same. So since we are assuming perfect branching (both target and direction),
      you do not have to handle RAW hazards for branches. 
	  Branch instructions occupy the IFQ but are never dispatched to reservation stations.
	  Branches can be removed from the IFQ once they reach the head."
	  -- Quoted from FAQ
  */
  
  // Always pick the head instr. in the queue to execute => in-order dispatch
  instruction_t* curr_instr = instr_queue[0];
  if(curr_instr == NULL) return; //// if instruction trace is complete, return
 
  if( IS_UNCOND_CTRL(curr_instr->op) || IS_COND_CTRL(curr_instr->op) ) { // occupy IFQ but are never actually dispatched into RS
	shift_ifq();
	curr_instr->tom_dispatch_cycle = current_cycle;
  }
  else if( (RS_tag = rs_not_full( curr_instr->op )) >= 0 ){   
 
	// Reservation space avilable
	
	// Allocate reservation station
	if( USES_INT_FU(curr_instr->op) && (RS_tag < RESERV_INT_SIZE)) {
		// Case 1 - Instr. is ALU/Load/Store
		reservINT[RS_tag] = curr_instr;
		
	}
	else if( USES_FP_FU(curr_instr->op) && (RS_tag < RESERV_FP_SIZE) ) {
		// Case 2 - Instr. is FP
		reservFP[RS_tag] = curr_instr;

	}
	
	// Check for RAW hazards
	// 1. scan through map table (MT) and check if any of
	//	the target register matches the source register
	//	in curr_instr
	// 2. RAW => store instr. containing the dest into the Q subfield
	//			 of current instr.
	for( i=0; i < 3; i++ ){
		// for each of the source registers in curr_instr
		// compare with each dest register in MT for RAW harzards
		if(curr_instr->r_in[i]!=DNA){
			if( map_table[ curr_instr->r_in[i] ] != NULL ){
				// found RAW hazards
				curr_instr->Q[RS_RAW++] = map_table[ curr_instr->r_in[i] ];
			}
		}
	}
	
	// Value copy in reservation is implicitly here
	
	// Update map table
	for( j=0; j < 2; j++ ){
		map_table[ (curr_instr->r_out[j]) ] = curr_instr;
	}
	
	// Update dispatch cycle
	curr_instr->tom_dispatch_cycle = current_cycle;
	
	// Dispatch and reduce IFQ
	shift_ifq();
  }
  
  /* ECE552 Assignment 3 - END CODE */  
}

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
	map_table[reg] = NULL;
  }
  
  int cycle = 0;
  while (true) {

     /* ECE552: YOUR CODE GOES HERE */
     /* ECE552 Assignment 3 - BEGIN CODE */

     cycle++;

     //Instruction Fetch: only one instruction can be fetched every cycle, as long as instruction queue is not full
     //Fetch and Dispatch are one single state  
     CDB_To_retire(cycle);

     execute_To_CDB(cycle);

     issue_To_execute(cycle);

     dispatch_To_issue(cycle);

     fetch_To_dispatch(trace, cycle); 
     
     /* ## DEBUGGER ## */
#ifdef DBG_VIEW
     DBG_viewCycle(cycle);
     DBG_viewIFQ_FUstatus();
     DBG_viewRS();
     DBG_viewMapTable_CDB();
#endif

     //if(cycle > 15)
     //	break;

     if (is_simulation_done(sim_num_insn)/*|| cycle > MAX_NUM_CYCLES*/)
        break;
  }

#ifdef DBG_VIEW
  DBG_viewCycleTable(trace, /*MAX_NUM_CYCLES*/ sim_num_insn);
#endif  

  return cycle;

  /* ECE552 Assignment 3 - END CODE */
}

/* ECE552 Assignment 3 - BEGIN CODE */

/* ECE552 Helper Functions */
// returns true if not full, else returns false
static bool ifq_not_full(void) { //TODO: maybe change this to macro later
	assert(instr_queue_size <= INSTR_QUEUE_SIZE);
	
	return (instr_queue_size < INSTR_QUEUE_SIZE)? true : false;
}

// Remove IFQ instruction 0 (first in queue) and shift the other instructions over 0 <- 1 <- 2 <- 3 ...
// and reduce ifq size
// TODO: Make sure array elements are within bounds
static void shift_ifq(){
	
	int i;
	instr_queue[0] = NULL;
	
	for( i=1; i < instr_queue_size; i++ ){
		instr_queue[i-1] = instr_queue[i];
	}
	instr_queue_size--;
	instr_queue[instr_queue_size] = NULL;
}
// Maybe add functions for checking if reservation stations are available

static int rs_not_full(enum md_opcode op){
	int i;
	
	if( USES_INT_FU(op) ){
		for( i=0; i < RESERV_INT_SIZE; i++ ){
			if( reservINT[i] == NULL ){
				return i;
			}
		}
	}
	else if( USES_FP_FU(op) ){
		for( i=0; i < RESERV_FP_SIZE; i++ ){
			if( reservFP[i] == NULL ){
				return i;
			}
		}
	}
	
	return -1;
}

static int fu_not_busy(enum md_opcode op) {
	int i;
	
	if( USES_INT_FU(op) ){
		for( i=0; i < FU_INT_SIZE; i++ ){
			if( fuINT[i] == NULL ){
				return i;
			}
		}
	}
	else if( USES_FP_FU(op) ){
		for( i=0; i < FU_FP_SIZE; i++ ){
			if( fuFP[i] == NULL ){
				return i;
			}
		}
	}
	
	return -1;
}

#ifdef DBG_VIEW

static void DBG_viewCycleTable(instruction_trace_t* trace, int num_instr){
    int i;
    instruction_t* instr = NULL;

    printf(" ########################################### Cycle Table ########################################### \n");
    printf("         Instr.                  index         dispatch       issue          execute           cdb \n");

    if( (num_instr < 1) || (num_instr > fetch_index)){
    	printf(" Specified cycle range exceeds the maximum \n");
	return;
    }

    for( i=1; i <= num_instr; i++ ){
    	instr = get_instr(trace, i);
	printf(" ");
	md_print_insn(instr->inst, 0, stdout);
	printf(" %-5s\t  %d \t\t  %d \t\t%d\t\t%d\t\t%d \n", "", instr->index, instr->tom_dispatch_cycle, instr->tom_issue_cycle, instr->tom_execute_cycle, instr->tom_cdb_cycle);
    }
}

static void DBG_viewCycle(int cycle){

     /* DEBUGGING */
     printf(" ######################################################################## \n");
     printf(" ############################### Cycle %d ############################### \n", cycle);
     printf(" ######################################################################## \n");
}

static void DBG_viewIFQ_FUstatus(){

     int i;
     /* IFQ and FU status table */
     printf(" -------------- IFQ ---------------   ");
     printf(" ------------ FU Status ----------- \n");
     printf(" IFQ#            Op         index           FU                  index \n");
     for( i=0; i < INSTR_QUEUE_SIZE; i++ ){
	
	if( i < FU_INT_SIZE ){
	
		printf(" IFQ #%d", i);
		if(instr_queue[i] != NULL){
          		printf(" \t%s\t      %d \t ", MD_OP_NAME(instr_queue[i]->op), instr_queue[i]->index);
			printf(" fuINT #%d \t", i);
			if(fuINT[i] != NULL){
				printf(" \t%s\t      %d \t ", MD_OP_NAME(fuINT[i]->op), fuINT[i]->index);
			}
			else{
				printf(" \t NULL ");
			}
       		}
		else{
        		printf(" \t NULL \t    NULL \t");
			printf(" fuINT #%d \t", i);
			if(fuINT[i] != NULL){
				printf(" \t%s\t      %d \t ", MD_OP_NAME(fuINT[i]->op), fuINT[i]->index);
			}
			else{
				printf(" \tNULL ");
			}
		}
		printf("\n");
	}
	else if( i < (FU_INT_SIZE + FU_FP_SIZE) ){
		
		printf(" IFQ #%d", i);
		if(instr_queue[i] != NULL){
          		printf(" \t%s\t      %d \t ", MD_OP_NAME(instr_queue[i]->op), instr_queue[i]->index);
		
			printf(" fuFP  #%d \t", (i - FU_INT_SIZE));
			if(fuFP[i - FU_INT_SIZE] != NULL){
				printf(" \t%s\t      %d \t ", MD_OP_NAME(fuFP[i - FU_INT_SIZE]->op), fuFP[i - FU_INT_SIZE]->index);
			}
			else{
				printf(" \t NULL ");
			}
       		}
		else{
        		printf(" \t NULL \t    NULL \t");
			printf(" fuFP  #%d \t", (i - FU_INT_SIZE));		
			if(fuFP[i - FU_INT_SIZE] != NULL){
				printf(" \t%s\t      %d \t ", MD_OP_NAME(fuFP[i - FU_INT_SIZE]->op), fuFP[i - FU_INT_SIZE]->index);
			}
			else{
				printf(" \t NULL ");
			}
		}
		printf("\n");
	}
	else{
		printf(" IFQ #%d", i);
		if(instr_queue[i] != NULL){
			printf(" \t%s\t      %d \t \n", MD_OP_NAME(instr_queue[i]->op), instr_queue[i]->index);
		}
		else{
			printf(" \t NULL \t    NULL \t\n");
		
		}
		
	}  
     }
     printf(" ------------------------------------------------------------------------ \n\n");
}

static void DBG_viewRS(){

     int i, j;
     /* RESERVATION STATION */
     printf(" ----------------------------- RESERVATION STATION ------------------------------- \n");
     printf("  Tag  |    FU     |    INSTR\t| R0\t| R1\t| T0\t| T1\t| T2\t| index\t| \n");
     for( i=0; i < RESERV_INT_SIZE; i++ ){
	if( reservINT[i] != NULL ){
		printf("   %d   |   %s   |    %s\t|", i, "intFU", MD_OP_NAME(reservINT[i]->op));
	
		for( j=0; j < 2; j++ ){
			if( reservINT[i]->r_out[j] == DNA ){
				printf(" DNA\t|");
			}
			else{
				printf(" r%d\t|", reservINT[i]->r_out[j]);
			}
		}
		for( j=0; j < 3; j++ ){
			if( reservINT[i]->Q[j] == NULL ){
				printf(" NULL\t|");
			}
			else{
				printf("  %d\t|", reservINT[i]->Q[j]->index);
			}
		}
		printf(" %d\t| \n", reservINT[i]->index);
	}
	else{
		printf("   %d   | \tNULL  \n", i);
	} 
     }

     for( i=0; i < RESERV_FP_SIZE; i++ ){
	if( reservFP[i] != NULL ){
		printf("   %d   |   %s    |    %s\t|", i, "fpFU", MD_OP_NAME(reservFP[i]->op));
	
		for( j=0; j < 2; j++ ){
			if( reservFP[i]->r_out[j] == DNA ){
				printf(" DNA\t|");
			}
			else{
				printf(" r%d\t|", reservFP[i]->r_out[j]);
			}
		}
		for( j=0; j < 3; j++ ){
			if( reservFP[i]->Q[j] == NULL ){
				printf(" NULL\t|");
			}
			else{
				printf("  %d\t|", reservFP[i]->Q[j]->index);
			}
		}
		printf(" %d\t| \n", reservFP[i]->index);
	}
	else{
		printf("   %d   | \t\t\t   NULL  \n", i);
	} 
     }
     printf(" --------------------------------------------------------------------------------- \n\n");
}

static void DBG_viewMapTable_CDB(){

     int i;
     bool DBG_isPrinted = false;
     /* Map table */
     printf(" ------------ Map table ------------   ");
     printf(" -------------- CDB -------------- \n");
     printf(" Register       index         Op \t  ");
     printf(" index                 Op \n");
     for( i=0; i < MD_TOTAL_REGS; i++ ){
	
	if( map_table[i] != NULL ){
     		printf("   r%d \t\t %d \t      %s      ", i, map_table[i]->index, MD_OP_NAME(map_table[i]->op));
		
		if( DBG_isPrinted == false ){
			if( commonDataBus != NULL ){
     				printf(" \t    %d                  %s ", commonDataBus->index, MD_OP_NAME(commonDataBus->op));
			}
			else{
     				printf(" \t    NULL                NULL ");
			}
			printf("\n");
			DBG_isPrinted = true;
		}
		else{
			printf("\n");
		}
	}
     }
     printf(" ------------------------------------------------------------------------- \n\n");
}
#endif


/* ####################### VERIFICATION ############################################## 

compress.eio trace exection instruction 18 to 27

 ########################################### Cycle Table ########################################### 
         Instr.                  index         dispatch       issue          execute           cdb 
 addiu     r29,r29,-24      	  18 		  32 		36		37		41        intFU               
 sw        r16,16(r29)      	  19 		  34 		41		42		0         RAW on r29
 addu      r16,r0,r5      	  20 		  35 		40		41		45        WAR on r16
 sw        r31,20(r29)      	  21 		  40 		44		45		0         RAW on r29
 beq       r16,r0,0x50      	  22 		  41 		0		0		0         RAW on r16 (cond. branch)
 lw        r4,0(r16)      	  23 		  42 		45		46		50        RAW on r16
 beq       r4,r0,0x40      	  24 		  43 		0		0		0         BR, RAW on r4
 addiu     r5,r0,47      	  25 		  44 		48		49		53        No dependencies
 jal       0x40b6c0      	  26 		  45 		0		0		0         No dependencies (uncond. branch)
 addiu     r29,r29,-32      	  27 		  46 		49		50		54 	  No hazards

The instr. #18 has a RAW dependency on 15 and it gets its value at cycle 35 and
will be issue at cycle 36
############################### Cycle 32 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      19 	  fuINT #0 	 	addu	      13 	 
 IFQ #1 	addu	      20 	  fuINT #1 	 	addiu	      15 	 
 IFQ #2 	sw	      21 	  fuFP  #0 	 	 NULL 
 IFQ #3 	beq	      22 	 
 IFQ #4 	lw	      23 	 
 IFQ #5 	beq	      24 	 
 IFQ #6 	addiu	      25 	 
 IFQ #7 	jal	      26 	 
 IFQ #8 	addiu	      27 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  15	| NULL	| NULL	| 16	| 
   1   |   intFU   |    addiu	| r29	| DNA	|  15	| NULL	| NULL	| 18	| 
   2   |   intFU   |    addu	| r6	| DNA	| NULL	| NULL	| NULL	| 13	| 
   3   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 15	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r6 		 13 	      addu       	    NULL                NULL 
   r29 		 18 	      addiu      
 ------------------------------------------------------------------------- 

 ############################### Cycle 33 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      19 	  fuINT #0 	 	addu	      13 	 
 IFQ #1 	addu	      20 	  fuINT #1 	 	addiu	      15 	 
 IFQ #2 	sw	      21 	  fuFP  #0 	 	 NULL 
 IFQ #3 	beq	      22 	 
 IFQ #4 	lw	      23 	 
 IFQ #5 	beq	      24 	 
 IFQ #6 	addiu	      25 	 
 IFQ #7 	jal	      26 	 
 IFQ #8 	addiu	      27 	 
 IFQ #9 	sw	      28 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  15	| NULL	| NULL	| 16	| 
   1   |   intFU   |    addiu	| r29	| DNA	|  15	| NULL	| NULL	| 18	| 
   2   |   intFU   |    addu	| r6	| DNA	| NULL	| NULL	| NULL	| 13	| 
   3   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 15	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r6 		 13 	      addu       	    NULL                NULL 
   r29 		 18 	      addiu      
 ------------------------------------------------------------------------- 

 ############################### Cycle 34 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addu	      20 	  fuINT #0 	 	 NULL 
 IFQ #1 	sw	      21 	  fuINT #1 	 	addiu	      15 	 
 IFQ #2 	beq	      22 	  fuFP  #0 	 	 NULL 
 IFQ #3 	lw	      23 	 
 IFQ #4 	beq	      24 	 
 IFQ #5 	addiu	      25 	 
 IFQ #6 	jal	      26 	 
 IFQ #7 	addiu	      27 	 
 IFQ #8 	sw	      28 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  15	| NULL	| NULL	| 16	| 
   1   |   intFU   |    addiu	| r29	| DNA	|  15	| NULL	| NULL	| 18	| 
   2   |   intFU   |    sw	| DNA	| DNA	|  18	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 15	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r29 		 18 	      addiu       	    13                  addu 
 ------------------------------------------------------------------------- 

 ############################### Cycle 35 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      21 	  fuINT #0 	 	 NULL 
 IFQ #1 	beq	      22 	  fuINT #1 	 	 NULL 
 IFQ #2 	lw	      23 	  fuFP  #0 	 	 NULL 
 IFQ #3 	beq	      24 	 
 IFQ #4 	addiu	      25 	 
 IFQ #5 	jal	      26 	 
 IFQ #6 	addiu	      27 	 
 IFQ #7 	sw	      28 	 
 IFQ #8 	andi	      29 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  15	| NULL	| NULL	| 16	| 
   1   |   intFU   |    addiu	| r29	| DNA	|  15	| NULL	| NULL	| 18	| 
   2   |   intFU   |    sw	| DNA	| DNA	|  18	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r16 		 20 	      addu       	    15                  addiu 
   r29 		 18 	      addiu      
 ------------------------------------------------------------------------- 

The instr #18 got its value from CDB and got issued.
 ############################### Cycle 36 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      21 	  fuINT #0 	 	sw	      16 	 
 IFQ #1 	beq	      22 	  fuINT #1 	 	addiu	      18 	 
 IFQ #2 	lw	      23 	  fuFP  #0 	 	 NULL 
 IFQ #3 	beq	      24 	 
 IFQ #4 	addiu	      25 	 
 IFQ #5 	jal	      26 	 
 IFQ #6 	addiu	      27 	 
 IFQ #7 	sw	      28 	 
 IFQ #8 	andi	      29 	 
 IFQ #9 	sw	      30 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 16	| 
   1   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 18	| 
   2   |   intFU   |    sw	| DNA	| DNA	|  18	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r16 		 20 	      addu       	    NULL                NULL 
   r29 		 18 	      addiu      
 ------------------------------------------------------------------------- 

 ############################### Cycle 37 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      21 	  fuINT #0 	 	sw	      16 	 
 IFQ #1 	beq	      22 	  fuINT #1 	 	addiu	      18 	 
 IFQ #2 	lw	      23 	  fuFP  #0 	 	 NULL 
 IFQ #3 	beq	      24 	 
 IFQ #4 	addiu	      25 	 
 IFQ #5 	jal	      26 	 
 IFQ #6 	addiu	      27 	 
 IFQ #7 	sw	      28 	 
 IFQ #8 	andi	      29 	 
 IFQ #9 	sw	      30 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 16	| 
   1   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 18	| 
   2   |   intFU   |    sw	| DNA	| DNA	|  18	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r16 		 20 	      addu       	    NULL                NULL 
   r29 		 18 	      addiu      
 ------------------------------------------------------------------------- 

 ############################### Cycle 38 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      21 	  fuINT #0 	 	sw	      16 	 
 IFQ #1 	beq	      22 	  fuINT #1 	 	addiu	      18 	 
 IFQ #2 	lw	      23 	  fuFP  #0 	 	 NULL 
 IFQ #3 	beq	      24 	 
 IFQ #4 	addiu	      25 	 
 IFQ #5 	jal	      26 	 
 IFQ #6 	addiu	      27 	 
 IFQ #7 	sw	      28 	 
 IFQ #8 	andi	      29 	 
 IFQ #9 	sw	      30 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 16	| 
   1   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 18	| 
   2   |   intFU   |    sw	| DNA	| DNA	|  18	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r16 		 20 	      addu       	    NULL                NULL 
   r29 		 18 	      addiu      
 ------------------------------------------------------------------------- 

 ############################### Cycle 39 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      21 	  fuINT #0 	 	sw	      16 	 
 IFQ #1 	beq	      22 	  fuINT #1 	 	addiu	      18 	 
 IFQ #2 	lw	      23 	  fuFP  #0 	 	 NULL 
 IFQ #3 	beq	      24 	 
 IFQ #4 	addiu	      25 	 
 IFQ #5 	jal	      26 	 
 IFQ #6 	addiu	      27 	 
 IFQ #7 	sw	      28 	 
 IFQ #8 	andi	      29 	 
 IFQ #9 	sw	      30 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 16	| 
   1   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 18	| 
   2   |   intFU   |    sw	| DNA	| DNA	|  18	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r16 		 20 	      addu       	    NULL                NULL 
   r29 		 18 	      addiu      
 ------------------------------------------------------------------------- 

instr. #18 finished execution broadcast to CDB
 ############################### Cycle 40 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	beq	      22 	  fuINT #0 	 	addu	      20 	 
 IFQ #1 	lw	      23 	  fuINT #1 	 	 NULL 
 IFQ #2 	beq	      24 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addiu	      25 	 
 IFQ #4 	jal	      26 	 
 IFQ #5 	addiu	      27 	 
 IFQ #6 	sw	      28 	 
 IFQ #7 	andi	      29 	 
 IFQ #8 	sw	      30 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 21	| 
   1   | 	NULL  
   2   |   intFU   |    sw	| DNA	| DNA	|  18	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r16 		 20 	      addu       	    18                  addiu 
 ------------------------------------------------------------------------- 

 branch instr. takes one cycle here causing one empty slot in the reservation station
 ############################### Cycle 41 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	lw	      23 	  fuINT #0 	 	addu	      20 	 
 IFQ #1 	beq	      24 	  fuINT #1 	 	sw	      19 	 
 IFQ #2 	addiu	      25 	  fuFP  #0 	 	 NULL 
 IFQ #3 	jal	      26 	 
 IFQ #4 	addiu	      27 	 
 IFQ #5 	sw	      28 	 
 IFQ #6 	andi	      29 	 
 IFQ #7 	sw	      30 	 
 IFQ #8 	sw	      31 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 21	| 
   1   | 	NULL  
   2   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r16 		 20 	      addu       	    NULL                NULL 
 ------------------------------------------------------------------------- 
 
 ############################### Cycle 42 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	beq	      24 	  fuINT #0 	 	addu	      20 	 
 IFQ #1 	addiu	      25 	  fuINT #1 	 	sw	      19 	 
 IFQ #2 	jal	      26 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addiu	      27 	 
 IFQ #4 	sw	      28 	 
 IFQ #5 	andi	      29 	 
 IFQ #6 	sw	      30 	 
 IFQ #7 	sw	      31 	 
 IFQ #8 	bne	      32 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 21	| 
   1   |   intFU   |    lw	| r4	| DNA	|  20	| NULL	| NULL	| 23	| 
   2   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r4 		 23 	      lw       	    NULL                NULL 
   r16 		 20 	      addu      
 ------------------------------------------------------------------------- 

 ############################### Cycle 43 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addiu	      25 	  fuINT #0 	 	addu	      20 	 
 IFQ #1 	jal	      26 	  fuINT #1 	 	sw	      19 	 
 IFQ #2 	addiu	      27 	  fuFP  #0 	 	 NULL 
 IFQ #3 	sw	      28 	 
 IFQ #4 	andi	      29 	 
 IFQ #5 	sw	      30 	 
 IFQ #6 	sw	      31 	 
 IFQ #7 	bne	      32 	 
 IFQ #8 	addu	      33 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 21	| 
   1   |   intFU   |    lw	| r4	| DNA	|  20	| NULL	| NULL	| 23	| 
   2   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addu	| r16	| DNA	| NULL	| NULL	| NULL	| 20	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r4 		 23 	      lw       	    NULL                NULL 
   r16 		 20 	      addu      
 ------------------------------------------------------------------------- 

 branch instr. takes one cycle here causing one empty slot in the reservation station
 ############################### Cycle 44 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	jal	      26 	  fuINT #0 	 	sw	      21 	 
 IFQ #1 	addiu	      27 	  fuINT #1 	 	sw	      19 	 
 IFQ #2 	sw	      28 	  fuFP  #0 	 	 NULL 
 IFQ #3 	andi	      29 	 
 IFQ #4 	sw	      30 	 
 IFQ #5 	sw	      31 	 
 IFQ #6 	bne	      32 	 
 IFQ #7 	addu	      33 	 
 IFQ #8 	addu	      34 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 21	| 
   1   |   intFU   |    lw	| r4	| DNA	|  20	| NULL	| NULL	| 23	| 
   2   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 19	| 
   3   |   intFU   |    addiu	| r5	| DNA	| NULL	| NULL	| NULL	| 25	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r4 		 23 	      lw       	    20                  addu 
   r5 		 25 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 45 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addiu	      27 	  fuINT #0 	 	sw	      21 	 
 IFQ #1 	sw	      28 	  fuINT #1 	 	lw	      23 	 
 IFQ #2 	andi	      29 	  fuFP  #0 	 	 NULL 
 IFQ #3 	sw	      30 	 
 IFQ #4 	sw	      31 	 
 IFQ #5 	bne	      32 	 
 IFQ #6 	addu	      33 	 
 IFQ #7 	addu	      34 	 
 IFQ #8 	jal	      35 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 21	| 
   1   |   intFU   |    lw	| r4	| DNA	| NULL	| NULL	| NULL	| 23	| 
   2   | 	NULL  
   3   |   intFU   |    addiu	| r5	| DNA	| NULL	| NULL	| NULL	| 25	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r4 		 23 	      lw       	    NULL                NULL 
   r5 		 25 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 46 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      28 	  fuINT #0 	 	sw	      21 	 
 IFQ #1 	andi	      29 	  fuINT #1 	 	lw	      23 	 
 IFQ #2 	sw	      30 	  fuFP  #0 	 	 NULL 
 IFQ #3 	sw	      31 	 
 IFQ #4 	bne	      32 	 
 IFQ #5 	addu	      33 	 
 IFQ #6 	addu	      34 	 
 IFQ #7 	jal	      35 	 
 IFQ #8 	addiu	      36 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 21	| 
   1   |   intFU   |    lw	| r4	| DNA	| NULL	| NULL	| NULL	| 23	| 
   2   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 27	| 
   3   |   intFU   |    addiu	| r5	| DNA	| NULL	| NULL	| NULL	| 25	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r4 		 23 	      lw       	    NULL                NULL 
   r5 		 25 	      addiu      
   r29 		 27 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 47 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      28 	  fuINT #0 	 	sw	      21 	 
 IFQ #1 	andi	      29 	  fuINT #1 	 	lw	      23 	 
 IFQ #2 	sw	      30 	  fuFP  #0 	 	 NULL 
 IFQ #3 	sw	      31 	 
 IFQ #4 	bne	      32 	 
 IFQ #5 	addu	      33 	 
 IFQ #6 	addu	      34 	 
 IFQ #7 	jal	      35 	 
 IFQ #8 	addiu	      36 	 
 IFQ #9 	andi	      37 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 21	| 
   1   |   intFU   |    lw	| r4	| DNA	| NULL	| NULL	| NULL	| 23	| 
   2   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 27	| 
   3   |   intFU   |    addiu	| r5	| DNA	| NULL	| NULL	| NULL	| 25	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r4 		 23 	      lw       	    NULL                NULL 
   r5 		 25 	      addiu      
   r29 		 27 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 48 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	andi	      29 	  fuINT #0 	 	addiu	      25 	 
 IFQ #1 	sw	      30 	  fuINT #1 	 	lw	      23 	 
 IFQ #2 	sw	      31 	  fuFP  #0 	 	 NULL 
 IFQ #3 	bne	      32 	 
 IFQ #4 	addu	      33 	 
 IFQ #5 	addu	      34 	 
 IFQ #6 	jal	      35 	 
 IFQ #7 	addiu	      36 	 
 IFQ #8 	andi	      37 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  27	| NULL	| NULL	| 28	| 
   1   |   intFU   |    lw	| r4	| DNA	| NULL	| NULL	| NULL	| 23	| 
   2   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 27	| 
   3   |   intFU   |    addiu	| r5	| DNA	| NULL	| NULL	| NULL	| 25	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r4 		 23 	      lw       	    NULL                NULL 
   r5 		 25 	      addiu      
   r29 		 27 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 49 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      30 	  fuINT #0 	 	addiu	      25 	 
 IFQ #1 	sw	      31 	  fuINT #1 	 	addiu	      27 	 
 IFQ #2 	bne	      32 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addu	      33 	 
 IFQ #4 	addu	      34 	 
 IFQ #5 	jal	      35 	 
 IFQ #6 	addiu	      36 	 
 IFQ #7 	andi	      37 	 
 IFQ #8 	andi	      38 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  27	| NULL	| NULL	| 28	| 
   1   |   intFU   |    andi	| r17	| DNA	|  25	| NULL	| NULL	| 29	| 
   2   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 27	| 
   3   |   intFU   |    addiu	| r5	| DNA	| NULL	| NULL	| NULL	| 25	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r5 		 25 	      addiu       	    23                  lw 
   r17 		 29 	      andi      
   r29 		 27 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 50 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      30 	  fuINT #0 	 	addiu	      25 	 
 IFQ #1 	sw	      31 	  fuINT #1 	 	addiu	      27 	 
 IFQ #2 	bne	      32 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addu	      33 	 
 IFQ #4 	addu	      34 	 
 IFQ #5 	jal	      35 	 
 IFQ #6 	addiu	      36 	 
 IFQ #7 	andi	      37 	 
 IFQ #8 	andi	      38 	 
 IFQ #9 	beq	      39 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  27	| NULL	| NULL	| 28	| 
   1   |   intFU   |    andi	| r17	| DNA	|  25	| NULL	| NULL	| 29	| 
   2   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 27	| 
   3   |   intFU   |    addiu	| r5	| DNA	| NULL	| NULL	| NULL	| 25	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r5 		 25 	      addiu       	    NULL                NULL 
   r17 		 29 	      andi      
   r29 		 27 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 51 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      30 	  fuINT #0 	 	addiu	      25 	 
 IFQ #1 	sw	      31 	  fuINT #1 	 	addiu	      27 	 
 IFQ #2 	bne	      32 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addu	      33 	 
 IFQ #4 	addu	      34 	 
 IFQ #5 	jal	      35 	 
 IFQ #6 	addiu	      36 	 
 IFQ #7 	andi	      37 	 
 IFQ #8 	andi	      38 	 
 IFQ #9 	beq	      39 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  27	| NULL	| NULL	| 28	| 
   1   |   intFU   |    andi	| r17	| DNA	|  25	| NULL	| NULL	| 29	| 
   2   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 27	| 
   3   |   intFU   |    addiu	| r5	| DNA	| NULL	| NULL	| NULL	| 25	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r5 		 25 	      addiu       	    NULL                NULL 
   r17 		 29 	      andi      
   r29 		 27 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 52 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	sw	      31 	  fuINT #0 	 	 NULL 
 IFQ #1 	bne	      32 	  fuINT #1 	 	addiu	      27 	 
 IFQ #2 	addu	      33 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addu	      34 	 
 IFQ #4 	jal	      35 	 
 IFQ #5 	addiu	      36 	 
 IFQ #6 	andi	      37 	 
 IFQ #7 	andi	      38 	 
 IFQ #8 	beq	      39 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  27	| NULL	| NULL	| 28	| 
   1   |   intFU   |    andi	| r17	| DNA	|  25	| NULL	| NULL	| 29	| 
   2   |   intFU   |    addiu	| r29	| DNA	| NULL	| NULL	| NULL	| 27	| 
   3   |   intFU   |    sw	| DNA	| DNA	|  27	| NULL	| NULL	| 30	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r17 		 29 	      andi       	    25                  addiu 
   r29 		 27 	      addiu      
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 53 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	bne	      32 	  fuINT #0 	 	andi	      29 	 
 IFQ #1 	addu	      33 	  fuINT #1 	 	 NULL 
 IFQ #2 	addu	      34 	  fuFP  #0 	 	 NULL 
 IFQ #3 	jal	      35 	 
 IFQ #4 	addiu	      36 	 
 IFQ #5 	andi	      37 	 
 IFQ #6 	andi	      38 	 
 IFQ #7 	beq	      39 	 
 IFQ #8 	lui	      40 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	|  27	| NULL	| NULL	| 28	| 
   1   |   intFU   |    andi	| r17	| DNA	| NULL	| NULL	| NULL	| 29	| 
   2   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 31	| 
   3   |   intFU   |    sw	| DNA	| DNA	|  27	| NULL	| NULL	| 30	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r17 		 29 	      andi       	    27                  addiu 
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 54 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addu	      33 	  fuINT #0 	 	andi	      29 	 
 IFQ #1 	addu	      34 	  fuINT #1 	 	sw	      28 	 
 IFQ #2 	jal	      35 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addiu	      36 	 
 IFQ #4 	andi	      37 	 
 IFQ #5 	andi	      38 	 
 IFQ #6 	beq	      39 	 
 IFQ #7 	lui	      40 	 
 IFQ #8 	ori	      41 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 28	| 
   1   |   intFU   |    andi	| r17	| DNA	| NULL	| NULL	| NULL	| 29	| 
   2   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 31	| 
   3   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 30	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r17 		 29 	      andi       	    NULL                NULL 
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 55 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addu	      33 	  fuINT #0 	 	andi	      29 	 
 IFQ #1 	addu	      34 	  fuINT #1 	 	sw	      28 	 
 IFQ #2 	jal	      35 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addiu	      36 	 
 IFQ #4 	andi	      37 	 
 IFQ #5 	andi	      38 	 
 IFQ #6 	beq	      39 	 
 IFQ #7 	lui	      40 	 
 IFQ #8 	ori	      41 	 
 IFQ #9 	sll	      42 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 28	| 
   1   |   intFU   |    andi	| r17	| DNA	| NULL	| NULL	| NULL	| 29	| 
   2   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 31	| 
   3   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 30	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r17 		 29 	      andi       	    NULL                NULL 
 ------------------------------------------------------------------------- 

 ######################################################################## 
 ############################### Cycle 56 ############################### 
 ######################################################################## 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addu	      33 	  fuINT #0 	 	andi	      29 	 
 IFQ #1 	addu	      34 	  fuINT #1 	 	sw	      28 	 
 IFQ #2 	jal	      35 	  fuFP  #0 	 	 NULL 
 IFQ #3 	addiu	      36 	 
 IFQ #4 	andi	      37 	 
 IFQ #5 	andi	      38 	 
 IFQ #6 	beq	      39 	 
 IFQ #7 	lui	      40 	 
 IFQ #8 	ori	      41 	 
 IFQ #9 	sll	      42 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 28	| 
   1   |   intFU   |    andi	| r17	| DNA	| NULL	| NULL	| NULL	| 29	| 
   2   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 31	| 
   3   |   intFU   |    sw	| DNA	| DNA	| NULL	| NULL	| NULL	| 30	| 
   0   | 			   NULL  
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r17 		 29 	      andi       	    NULL                NULL 
 ------------------------------------------------------------------------- 


 ########################################### Cycle Table ###########################################
                                               (cycle #)        (cycle #)      (cycle #)        (cycle #)
         Instr.                  index         dispatch         issue          execute           cdb 
 addu      r6,r0,r0      	 10911 		 19357 		19361		19362		19366 
 mtc1      r7,f2      	  	 10912 		 19358 		19365		19366		19370 
 cvt.d.w   f2,f2      	  	 10913 		 19359 		19370		19371		19380 <-- FP instr.
 addu      r7,r0,r10      	 10914 		 19361 		19362		19363		19367 
 addu      r3,r0,r8      	 10915 		 19362 		19366		19367		19371 

 r34 is equivalent to f2 as it is offset by 32
 instr. ctv.d.w is dispatched into RS in this cycle and it depends on the output of instr. #10912, which
 is the mtc1 int-to-FP conversion instr.
 ############################### Cycle 19359 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addu	      10914 	  fuINT #0 	 	addiu	      10910 	 
 IFQ #1 	addu	      10915 	  fuINT #1 	 	slti	      10907 	 
 IFQ #2 	l.s	      10916 	  fuFP  #0 	 	 NULL 
 IFQ #3 	cvt.d.w	      10917 	 
 IFQ #4 	div.d	      10918 	 
 IFQ #5 	addiu	      10919 	 
 IFQ #6 	addiu	      10920 	 
 IFQ #7 	slti	      10921 	 
 IFQ #8 	s.d	      10922 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    mtc1	| r34	| DNA	|  10910	| NULL	| NULL	| 10912	| 
   1   |   intFU   |    addiu	| r7	| DNA	| NULL	| NULL	| NULL	| 10910	| 
   2   |   intFU   |    addu	| r6	| DNA	| NULL	| NULL	| NULL	| 10911	| 
   3   |   intFU   |    slti	| r2	| DNA	| NULL	| NULL	| NULL	| 10907	| 
   0   |   fpFU    |    cvt.d.w	| r34	| DNA	|  10912	| NULL	| NULL	| 10913	| 
   1   | 			   NULL  
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r2 		 10907 	      slti       	    NULL                NULL 
   r6 		 10911 	      addu      
   r7 		 10910 	      addiu      
   r34 		 10913 	      cvt.d.w      
 ------------------------------------------------------------------------- 

 ..

 instr. mtc1 finished execution and f2 is sent to CDB and will be available in the
 next cycle
 ############################### Cycle 19369 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	div.d	      10918 	  fuINT #0 	 	addu	      10915 	 
 IFQ #1 	addiu	      10919 	  fuINT #1 	 	 NULL 
 IFQ #2 	addiu	      10920 	  fuFP  #0 	 	 NULL 
 IFQ #3 	slti	      10921 	 
 IFQ #4 	s.d	      10922 	 
 IFQ #5 	addiu	      10923 	 
 IFQ #6 	bne	      10924 	 
 IFQ #7 	l.s	      10925 	 
 IFQ #8 	cvt.d.w	      10926 	 
 IFQ #9 	div.d	      10927 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   | 	NULL  
   1   |   intFU   |    addu	| r3	| DNA	| NULL	| NULL	| NULL	| 10915	| 
   2   |   intFU   |    l.s	| r32	| DNA	|  10915	| NULL	| NULL	| 10916	| 
   3   | 	NULL  
   0   |   fpFU    |    cvt.d.w	| r34	| DNA	|  10912	| NULL	| NULL	| 10913	| 
   1   |   fpFU    |    cvt.d.w	| r32	| DNA	|  10916	| NULL	| NULL	| 10917	| 
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r3 		 10915 	      addu       	    10912                  mtc1 
   r32 		 10917 	      cvt.d.w      
   r34 		 10913 	      cvt.d.w      
 ------------------------------------------------------------------------- 

 the dependency in the cvt.d.w on f2 is removed as CDB broadcasts f2
 in the same cycle cvt.d.w is issued
 ############################### Cycle 19370 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	div.d	      10918 	  fuINT #0 	 	 NULL 
 IFQ #1 	addiu	      10919 	  fuINT #1 	 	 NULL 
 IFQ #2 	addiu	      10920 	  fuFP  #0 	 	cvt.d.w	      10913 	 
 IFQ #3 	slti	      10921 	 
 IFQ #4 	s.d	      10922 	 
 IFQ #5 	addiu	      10923 	 
 IFQ #6 	bne	      10924 	 
 IFQ #7 	l.s	      10925 	 
 IFQ #8 	cvt.d.w	      10926 	 
 IFQ #9 	div.d	      10927 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   | 	NULL  
   1   | 	NULL  
   2   |   intFU   |    l.s	| r32	| DNA	|  10915	| NULL	| NULL	| 10916	| 
   3   | 	NULL  
   0   |   fpFU    |    cvt.d.w	| r34	| DNA	| NULL	| NULL	| NULL	| 10913	| 
   1   |   fpFU    |    cvt.d.w	| r32	| DNA	|  10916	| NULL	| NULL	| 10917	| 
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r32 		 10917 	      cvt.d.w       	    10915                  addu 
   r34 		 10913 	      cvt.d.w      
 ------------------------------------------------------------------------- 

 cvt.d.w starts execution
 ############################### Cycle 19371 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	div.d	      10918 	  fuINT #0 	 	l.s	      10916 	 
 IFQ #1 	addiu	      10919 	  fuINT #1 	 	 NULL 
 IFQ #2 	addiu	      10920 	  fuFP  #0 	 	cvt.d.w	      10913 	 
 IFQ #3 	slti	      10921 	 
 IFQ #4 	s.d	      10922 	 
 IFQ #5 	addiu	      10923 	 
 IFQ #6 	bne	      10924 	 
 IFQ #7 	l.s	      10925 	 
 IFQ #8 	cvt.d.w	      10926 	 
 IFQ #9 	div.d	      10927 	 
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   | 	NULL  
   1   | 	NULL  
   2   |   intFU   |    l.s	| r32	| DNA	| NULL	| NULL	| NULL	| 10916	| 
   3   | 	NULL  
   0   |   fpFU    |    cvt.d.w	| r34	| DNA	| NULL	| NULL	| NULL	| 10913	| 
   1   |   fpFU    |    cvt.d.w	| r32	| DNA	|  10916	| NULL	| NULL	| 10917	| 
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r32 		 10917 	      cvt.d.w       	    NULL                NULL 
   r34 		 10913 	      cvt.d.w      
 -------------------------------------------------------------------------

 ..

 9 cycles later the cvt.d.w i.e. instr. #10913 finished execution (FP instr. takes 9 cycles to complete)
 it rewrites to CDB and will be available in the next cycle
 ############################### Cycle 19379 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addiu	      10919 	  fuINT #0 	 	 NULL 
 IFQ #1 	addiu	      10920 	  fuINT #1 	 	 NULL 
 IFQ #2 	slti	      10921 	  fuFP  #0 	 	cvt.d.w	      10917 	 
 IFQ #3 	s.d	      10922 	 
 IFQ #4 	addiu	      10923 	 
 IFQ #5 	bne	      10924 	 
 IFQ #6 	l.s	      10925 	 
 IFQ #7 	cvt.d.w	      10926 	 
 IFQ #8 	div.d	      10927 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   | 	NULL  
   1   | 	NULL  
   2   | 	NULL  
   3   | 	NULL  
   0   |   fpFU    |    div.d	| r32	| DNA	|  10917	| NULL	| NULL	| 10918	| 
   1   |   fpFU    |    cvt.d.w	| r32	| DNA	| NULL	| NULL	| NULL	| 10917	| 
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r32 		 10918 	      div.d       	    10913                  cvt.d.w 
 ------------------------------------------------------------------------- 

 CDB value finished broadcasting
 ############################### Cycle 19380 ############################### 
 -------------- IFQ ---------------    ------------ FU Status ----------- 
 IFQ#            Op         index           FU                  index 
 IFQ #0 	addiu	      10920 	  fuINT #0 	 	 NULL 
 IFQ #1 	slti	      10921 	  fuINT #1 	 	 NULL 
 IFQ #2 	s.d	      10922 	  fuFP  #0 	 	cvt.d.w	      10917 	 
 IFQ #3 	addiu	      10923 	 
 IFQ #4 	bne	      10924 	 
 IFQ #5 	l.s	      10925 	 
 IFQ #6 	cvt.d.w	      10926 	 
 IFQ #7 	div.d	      10927 	 
 IFQ #8 	addiu	      10928 	 
 IFQ #9 	 NULL 	    NULL 	
 ------------------------------------------------------------------------ 

 ----------------------------- RESERVATION STATION ------------------------------- 
  Tag  |    FU     |    INSTR	| R0	| R1	| T0	| T1	| T2	| index	| 
   0   |   intFU   |    addiu	| r3	| DNA	| NULL	| NULL	| NULL	| 10919	| 
   1   | 	NULL  
   2   | 	NULL  
   3   | 	NULL  
   0   |   fpFU    |    div.d	| r32	| DNA	|  10917	| NULL	| NULL	| 10918	| 
   1   |   fpFU    |    cvt.d.w	| r32	| DNA	| NULL	| NULL	| NULL	| 10917	| 
 --------------------------------------------------------------------------------- 

 ------------ Map table ------------    -------------- CDB -------------- 
 Register       index         Op 	   index                 Op 
   r3 		 10919 	      addiu       	    NULL                NULL 
   r32 		 10918 	      div.d      
 ------------------------------------------------------------------------- 

*/

/* ECE552 Assignment 3 - END CODE */


