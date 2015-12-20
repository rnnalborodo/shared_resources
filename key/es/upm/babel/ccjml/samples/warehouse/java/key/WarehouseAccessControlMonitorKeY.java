package es.upm.babel.ccjml.samples.warehouse.java.key;
/** 
 * WarehouseAccessControl implementation using Babel Priority Monitors.
 * Instrumented to be verifiable in KeY
 * 
 * Naive implementation
 * Parameter indexation for robots entering to warehouse.
 * Parameter indexation for leaving a warehouse n.
 * 
 * @author BABEL Group - Technical University of Madrid
 */

public class WarehouseAccessControlMonitorKeY {
  
  //@ ghost int awakenThread;
  
  public static final int N_ROBOTS = 2;
  public static final int N_WAREHOUSE = 4;
  public static final int MAX_WEIGHT_IN_WAREHOUSE = 10;
  public static final int EMPTY_WEIGHT = 1;
  
  // INNER STATE ATTRIBUTES
  //@ public invariant corridor.length == N_WAREHOUSE;
  private /*@ spec_public @*/ boolean corridor[];
  
  /*@ public invariant (\forall int i; i >=0 && i<= N_WAREHOUSE; 
    @                            warehouseCurrentWeight[i] >= 0 && 
    @                            warehouseCurrentWeight[i] <= MAX_WEIGHT_IN_WAREHOUSE)
    @                  && warehouseCurrentWeight.length == N_WAREHOUSE;
    @*/
  private /*@ spec_public @*/int warehouseCurrentWeight[];
      
  // Monitor & conditions definition
  /*@ public invariant (\forall int i; i >=0 && i<= N_WAREHOUSE; 
    @                     enteringWarehouse[i].length == MAX_WEIGHT_IN_WAREHOUSE 
    @                     &&  (\forall int j;j >=0 && j<= MAX_WEIGHT_IN_WAREHOUSE;
    @                            enteringWarehouse[i][j] >= 0)
    @                  )
    @                  && enteringWarehouse.length == N_WAREHOUSE;
    @*/
	private /*@ spec_public @*/int enteringWarehouse[][];
	    
  /*@ public invariant (\forall int i; i >=0 && i<= N_WAREHOUSE; exitingWarehouse[i] >= 0)
    @                  && exitingWarehouse.length == N_WAREHOUSE;	 
	  @*/
	private /*@ spec_public @*/ int exitingWarehouse[];
	
	//@ public invariant signaled == 0 || signaled == 1;
  private /*@ spec_public @*/ int signaled;

	//@ requires warehouse >0 && warehouse <= N_WAREHOUSE;
	//@ requires weight >=0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;
  //@ requires warehouse == 0 || !corridor[warehouse-1] ; // VER!!! split? lazy
	//@ assignable enteringWarehouse[0][*]; 
	//@ assignable exitingWarehouse[((warehouse == 0)?0:warehouse-1)];
	//@ diverges false;
  //prop_safe_signal
  /*@ ensures
    @  (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE; 
    @        (enteringWarehouse[0][i] + 1 == \old(enteringWarehouse)[0][i] ==> 
    @                  warehouseCurrentWeight[warehouse-1] + i <= MAX_WEIGHT_IN_WAREHOUSE))
    @  &&
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (exitingWarehouse[i] + 1 == \old(exitingWarehouse)[i] 
    @                  ==> i+1 != N_WAREHOUSE -1 && corridor[i])
    @  );
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @    (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE; i != N_WAREHOUSE - awakenThread ==>
    @                   (enteringWarehouse[0][i] == 
    @                        \old(enteringWarehouse)[0][i]))
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @                   exitingWarehouse[i] == \old(exitingWarehouse)[i]
    @    ) 
    @  && 
    @  ( awakenThread != -1 ==> (
    @    ( awakenThread > N_WAREHOUSE ==> 
    @        (enteringWarehouse[0][N_WAREHOUSE - awakenThread] + 1 
    @          == \old(enteringWarehouse)[0][N_WAREHOUSE - awakenThread]))
    @    ||
    @    (awakenThread <= N_WAREHOUSE ==> exitingWarehouse[awakenThread] + 1== \old(exitingWarehouse)[awakenThread])
    @    )
    @  )
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @     enteringWarehouse[0][N_WAREHOUSE - awakenThread] + 1 ==
    @           \old(enteringWarehouse[0][N_WAREHOUSE - awakenThread]) ||
    @     exitingWarehouse[awakenThread] + 1== \old(exitingWarehouse)[awakenThread]
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  ( awakenThread != -1 && 
    @      (awakenThread > N_WAREHOUSE ==> 
    @         ((\old(enteringWarehouse)[0][N_WAREHOUSE - awakenThread] > 0
    @         && warehouseCurrentWeight[0] + N_WAREHOUSE - awakenThread <= MAX_WEIGHT_IN_WAREHOUSE
    @      ) && 
    @      (awakenThread <= N_WAREHOUSE ==>
    @         (\old(exitingWarehouse)[awakenThread] > 0 && 
    @                 awakenThread + 1 != N_WAREHOUSE -1 && corridor[awakenThread]))
    @      ))
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
	public void unblockingCodeEnterWarehouse(int warehouse, int weight) {
	  //@ set awakenThread = -1;
	  signaled = 0;
		if (warehouse == 0){
  	  int from = MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse];
	    /*@ loop_invariant
        @   currentWeight >= 0 && currentWeight < MAX_WEIGHT_IN_WAREHOUSE &&
        @   (\forall int j; 0<= j && j < currentWeight; enteringWarehouse[warehouse][j] == 0 );
        @ assignable enteringWarehouse[warehouse][*];
        @ decreasing MAX_WEIGHT_IN_WAREHOUSE - currentWeight ;
        @*/
  		for (int currentWeight = from; currentWeight < MAX_WEIGHT_IN_WAREHOUSE; currentWeight++){
  			if (enteringWarehouse[warehouse][currentWeight] > 0 ){
  				  enteringWarehouse[warehouse][currentWeight]--;
  				  //@ set awakenThread = N_WAREHOUSE + currentWeight;
  				  signaled++;
  				  break;
  			}
  		}
		} else { // exiting could perform iff a robot enter to any warehouse but the first 
			if (exitingWarehouse[warehouse-1]> 0)
				exitingWarehouse[warehouse-1]--;
			  //@ set awakenThread = warehouse - 1;
			  signaled ++;
		}
	}

	//@ requires warehouse >=0 && warehouse <= N_WAREHOUSE;
  //@ requires weight >=0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;
	//@ requires corridor[warehouse-1]; // post of exitWarehouse
  //@ assignable enteringWarehouse[0][*];
	//@ diverges false;
  //prop_safe_signal
  /*@ ensures
    @  (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE; 
    @        enteringWarehouse[(warehouse == 0)?0:warehouse-1][i] + 1 == \old(enteringWarehouse)[(warehouse == 0)?0:warehouse-1][i] ==>
    @                     warehouseCurrentWeight[warehouse-1] + i <= MAX_WEIGHT_IN_WAREHOUSE
    @  );
    @*/
	 // prop_signal_0_1
  /*@ ensures 
    @    (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE; i != awakenThread ==>
    @                   (enteringWarehouse[(warehouse == 0)?0:warehouse-1][i] ==
    @                      \old(enteringWarehouse)[(warehouse == 0)?0:warehouse-1][i] )
    @    ) 
    @  && 
    @  ( awakenThread != -1 ==> 
    @    enteringWarehouse[(warehouse == 0)?0:warehouse-1][awakenThread] + 1== 
    @           \old(enteringWarehouse)[(warehouse == 0)?0:warehouse-1][awakenThread]
    @  )
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @     enteringWarehouse[(warehouse == 0)?0:warehouse-1][awakenThread] + 1 ==
    @           \old(enteringWarehouse[(warehouse == 0)?0:warehouse-1][awakenThread])
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  ( awakenThread != -1 && \old(enteringWarehouse)[(warehouse == 0)?0:warehouse-1][awakenThread] > 0
    @   && warehouseCurrentWeight[warehouse-1] + awakenThread <= MAX_WEIGHT_IN_WAREHOUSE
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
	public void unblockingCodeExitWarehouse(int warehouse, int weight) {
	  signaled = 0;
	  //@ set awakenThread = -1;
		// unblocking code 
		int wid = (warehouse == 0)?0:warehouse-1;
    int from = MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[wid];
    /*@ loop_invariant
      @   currentWeight >= 0 && currentWeight < MAX_WEIGHT_IN_WAREHOUSE &&
      @   (\forall int j; 0<= j && j < currentWeight; enteringWarehouse[wid][j] == 0 );
      @ assignable enteringWarehouse[wid][*];
      @ decreasing MAX_WEIGHT_IN_WAREHOUSE - currentWeight ;
      @*/
    for (int currentWeight = from; currentWeight < MAX_WEIGHT_IN_WAREHOUSE; currentWeight++){
      if (enteringWarehouse[wid][from] > 0 ){
          enteringWarehouse[wid][from ]--;
          //@ set awakenThread = from;
          signaled++;
          break;
      }
    }
  }     

}