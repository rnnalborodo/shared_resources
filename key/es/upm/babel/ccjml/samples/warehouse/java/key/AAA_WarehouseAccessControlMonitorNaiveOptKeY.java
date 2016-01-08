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

public class AAA_WarehouseAccessControlMonitorNaiveOptKeY {
  
  //@ ghost int awakenThread;
  
  public static final int N_ROBOTS = 2;
  public static final int N_WAREHOUSE = 4;
  public static final int MAX_WEIGHT_IN_WAREHOUSE = 5;
  public static final int EMPTY_WEIGHT = 1;
  
  // INNER STATE ATTRIBUTES
  //@ public invariant corridor.length == N_WAREHOUSE;
  //true -> free corridor
  private /*@ spec_public @*/ boolean corridor[];
  
  /*@ public invariant (\forall int i; i >=0 && i< N_WAREHOUSE; 
    @                            warehouseCurrentWeight[i] >= 0 && 
    @                            warehouseCurrentWeight[i] <= MAX_WEIGHT_IN_WAREHOUSE)
    @                  && warehouseCurrentWeight.length == N_WAREHOUSE;
    @*/
  private /*@ spec_public @*/int warehouseCurrentWeight[];
      
  // Monitor & conditions definition
  /*@ public invariant (\forall int i; i >=0 && i< N_WAREHOUSE; 
    @                     enteringWarehouse[i].length == MAX_WEIGHT_IN_WAREHOUSE 
    @                     &&  (\forall int j;j >=0 && j< MAX_WEIGHT_IN_WAREHOUSE;
    @                            enteringWarehouse[i][j] >= 0)
    @                  )
    @                  && enteringWarehouse.length == N_WAREHOUSE;
    @*/
  private /*@ spec_public @*/int enteringWarehouse[][];
      
  /*@ public invariant (\forall int i; i >=0 && i< N_WAREHOUSE; exitingWarehouse[i] >= 0)
    @                  && exitingWarehouse.length == N_WAREHOUSE;   
    @*/
  private /*@ spec_public @*/ int exitingWarehouse[];
  
  //@ public invariant signaled == 0 || signaled == 1;
  private /*@ spec_public @*/ int signaled;

  //@ requires warehouse >= 0 && warehouse < N_WAREHOUSE;
  //@ requires warehouse == 0;
  //@ requires weight > 0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;

  //@ assignable signaled, awakenThread;
  //@ assignable exitingWarehouse[((warehouse == 0)?0:warehouse-1)];
  //@ assignable enteringWarehouse[warehouse][*];

  public void unblockingCodeEnterWarehouse(int warehouse, int weight) {
    //@ set awakenThread = -1;
    signaled = 0;
    if (warehouse == 0){
      int availableWeight = MAX_WEIGHT_IN_WAREHOUSE ;
      /*@ loop_invariant 
        @    (i >= 0 && i <= MAX_WEIGHT_IN_WAREHOUSE && 
        @         (\forall int j; j >= 0 && j < i ; enteringWarehouse[warehouse][j] == 1 ));
        @ assignable enteringWarehouse[warehouse][*];
        @ decreases enteringWarehouse[warehouse].length - i;
        @*/
      for (int i = 0; i < availableWeight ; i++ ) {
        enteringWarehouse[warehouse][i] = 1;
        break;
      }
    }
  }
  
  //@ requires warehouse >= 0 && warehouse < N_WAREHOUSE;
  //@ requires weight > 0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;
  //@ requires warehouse > 0 ==> !corridor[warehouse] ;

  //@ assignable signaled, awakenThread;
  //@ assignable exitingWarehouse[((warehouse == 0)?0:warehouse-1)];
  //@ assignable enteringWarehouse[0][*];
  //@ diverges false;
  //prop_safe_signal -> VERIFIED
  /*@ ensures
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (exitingWarehouse[i] + 1 == \old(exitingWarehouse[i]) 
    @                  ==> ( i+1 != N_WAREHOUSE && !corridor[i]) 
    @        )
    @  );
    @*/
  // prop_signal_0_1 -> VERIFIED!
  /* @ ensures 
    @    (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE; i != N_WAREHOUSE - awakenThread ==>
    @                   (enteringWarehouse[0][i] == 
    @                        \old(enteringWarehouse[0][i]))
    @    )
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; i != awakenThread ==>
    @                   exitingWarehouse[i] == \old(exitingWarehouse[i])
    @    ) 
    @  && 
    @  ( awakenThread != -1 ==> 
    @    (
    @      ( awakenThread > N_WAREHOUSE ==> 
    @          (enteringWarehouse[0][N_WAREHOUSE - awakenThread] + 1 
    @            == \old(enteringWarehouse[0][N_WAREHOUSE - awakenThread])
    @          )
    @      )
    @      ||
    @      (
    @        awakenThread <= N_WAREHOUSE ==> 
    @              exitingWarehouse[awakenThread] + 1== \old(exitingWarehouse[awakenThread])
    @      )
    @    )
    @  )
    @  ;
    @*/
  // prop_signal_effective -> VERIFIED!
  /* @ ensures
    @  signaled == 1
    @  ==>
    @  (
    @    (enteringWarehouse[0][N_WAREHOUSE - awakenThread] + 1 ==
    @           \old(enteringWarehouse[0][N_WAREHOUSE - awakenThread])) ||
    @    (exitingWarehouse[awakenThread] + 1 == \old(exitingWarehouse[awakenThread]))
    @  );
    @*/
  // prop_liveness -> VERIFIED!
  /* @ ensures
    @  ( awakenThread != -1 && 
    @    (   
    @      (awakenThread <= N_WAREHOUSE ==>
    @             (\old(exitingWarehouse)[awakenThread] > 0 && 
    @                 awakenThread + 1 != N_WAREHOUSE && !corridor[awakenThread]
    @             )
    @      )
    @    )
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
  private void _unblockingCodeEnterWarehouse(int warehouse, int weight){
    //@ set awakenThread = -1;
    signaled = 0;
    if (warehouse == 0){
      
    } else { // exiting could perform iff a robot enter to any warehouse but the first
      
      if (exitingWarehouse[warehouse-1]> 0 && !corridor[warehouse]){
        exitingWarehouse[warehouse-1]--;
        //@ set awakenThread = warehouse - 1;
        signaled ++;
      }
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
    int availableWeight = MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[wid];
    /*@ loop_invariant
      @   currentWeight >= 0 && currentWeight <= availableWeight &&
      @   (\forall int j; currentWeight < j && j <= availableWeight; enteringWarehouse[wid][j] == 0 );
      @ assignable enteringWarehouse[wid][*];
      @ decreasing currentWeight ;
      @*/

    for (int currentWeight = availableWeight; currentWeight > 0; currentWeight--){
      if (enteringWarehouse[wid][availableWeight] > 0 ){
          enteringWarehouse[wid][currentWeight ]--;
          //@ set awakenThread = currentWeight;
          signaled++;
          break;
      }
    }
  }     

}