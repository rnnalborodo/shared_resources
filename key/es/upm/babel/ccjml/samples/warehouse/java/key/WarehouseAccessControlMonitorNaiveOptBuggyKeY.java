package es.upm.babel.ccjml.samples.warehouse.java.key;

/** 
 * WarehouseAccessControl implementation using Priority Monitors library.
 * Instrumented to be verifiable in KeY
 *
 * Naive implementation with optimized unblocking code
 * Parameter indexation for robots entering to warehouse.
 * Parameter indexation for leaving a warehouse n.
 * 
 * @author Raul Alborodo - BABEL Group - Technical University of Madrid
 */

public class WarehouseAccessControlMonitorNaiveOptKeY {
  
  //@ ghost int awakenThreadC;
  //@ ghost int awakenThreadR;
  
  //@ public invariant N_WAREHOUSE > 0;
  public static final int N_WAREHOUSE = 4;
  //@ public invariant MAX_WEIGHT_IN_WAREHOUSE > 0;
  public static final int MAX_WEIGHT_IN_WAREHOUSE = 10;
  
  // INNER STATE ATTRIBUTES
  
  //@ public invariant corridor.length == N_WAREHOUSE - 1;
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
    @                     &&  (\forall int j;j >=0 && j< MAX_WEIGHT_IN_WAREHOUSE;
    @                            enteringWarehouse[i][j] >= 0)
    @                  )
    @                  && enteringWarehouse.length == N_WAREHOUSE;
    @*/
  private /*@ spec_public @*/int enteringWarehouse[][];
      
  /*@ public invariant (\forall int i; i >=0 && i<= N_WAREHOUSE; 
    @                                                 exitingWarehouse[i] >= 0)
    @                  && exitingWarehouse.length == N_WAREHOUSE;   
    @*/
  private /*@ spec_public @*/ int exitingWarehouse[];
  
  //@ public invariant signaled == 0 || signaled == 1;
  private /*@ spec_public @*/ int signaled;

  //@ requires warehouse >= 0 && warehouse < N_WAREHOUSE;
  //derived from POST 
  //@ requires warehouse > 0 ==> !corridor[warehouse-1]; 
  //@ assignable enteringWarehouse[*]; 
  //@ assignable exitingWarehouse[*];
  //@ diverges false;
  //prop_safe_signal
  /*@ ensures
    @  (\forall int j; j>=0 && j < N_WAREHOUSE;
    @    (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE + 1; 
    @        (enteringWarehouse[j][i] + 1 == \old(enteringWarehouse)[j][i] ==> 
    @                  warehouseCurrentWeight[j] + i <= MAX_WEIGHT_IN_WAREHOUSE)
    @    )
    @  )
    @  &&
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (exitingWarehouse[i] + 1 == \old(exitingWarehouse)[i] 
    @                  ==> ((i != N_WAREHOUSE -1 && corridor[i]) || i == N_WAREHOUSE -1)
    @        )
    @  );
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @  (\forall int j; j>=0 && j < N_WAREHOUSE;
    @    (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE +1; i != N_WAREHOUSE - awakenThreadC ==>
    @                   (enteringWarehouse[j][i] == 
    @                        \old(enteringWarehouse[j][i]))
    @    )
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @           i != awakenThreadC ==> exitingWarehouse[i] == \old(exitingWarehouse)[i]
    @    )
    @  ) 
    @  && 
    @  ( awakenThreadC != -1 ==> (
    @    ( awakenThreadC > N_WAREHOUSE ==> 
    @        (enteringWarehouse[N_WAREHOUSE - awakenThreadC][awakenThreadR] + 1 
    @          == \old(enteringWarehouse)[N_WAREHOUSE - awakenThreadC][awakenThreadR]))
    @    ||
    @    (awakenThreadC <= N_WAREHOUSE ==> 
    @             exitingWarehouse[awakenThreadC] + 1== \old(exitingWarehouse)[awakenThreadC])
    @    )
    @  )
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @    ( awakenThreadC > N_WAREHOUSE ==> 
    @      enteringWarehouse[N_WAREHOUSE - awakenThreadC][awakenThreadR] + 1 ==
    @           \old(enteringWarehouse[N_WAREHOUSE - awakenThreadC][awakenThreadR])) 
    @  &&
    @    (awakenThreadC <= N_WAREHOUSE ==> 
    @      exitingWarehouse[awakenThreadC] + 1== \old(exitingWarehouse[awakenThreadC])
    @    )
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  ( awakenThreadC != -1 && 
    @      ( awakenThreadC > N_WAREHOUSE ==> 
    @         (\old(enteringWarehouse[N_WAREHOUSE - awakenThreadC][awakenThreadR]) > 0
    @          && warehouseCurrentWeight[N_WAREHOUSE - awakenThreadC] + awakenThreadR <= MAX_WEIGHT_IN_WAREHOUSE
    @         )
    @      ) && 
    @      (awakenThreadC <= N_WAREHOUSE ==>
    @         (\old(exitingWarehouse)[awakenThreadC] > 0 && 
    @           (
    @             (awakenThreadC != N_WAREHOUSE -1 && corridor[awakenThreadC]) ||
    @             (awakenThreadC == N_WAREHOUSE -1)    
    @           )
    @         )
    @      )
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
  private void enterWarehouseUnblockingCode(int warehouse){
    //@ set awakenThreadC = -1;
    signaled = 0;

    // unblocking code
    // trying to wake up enterWarehouse calls
    if (warehouse == 0){
      // only enterWarehouse 0 can be awakened
      int availableWeight = MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse];
      if (availableWeight > 0) {
        /*@ loop_invariant 
          @    ((currentWeight >= 1 && currentWeight <= availableWeight + 1) || signaled == 1) && 
          @         (\forall int l; l >= 1 && l < currentWeight ; enteringWarehouse[warehouse][l] == 0) &&
          @         (awakenThreadC != -1 ==> signaled == 1);
          @ assignable enteringWarehouse[warehouse][1..availableWeight];
          @ decreases availableWeight - currentWeight;
          @*/  
        for (int currentWeight = 1; currentWeight <= availableWeight && signaled == 0; currentWeight++){
          if (enteringWarehouse[warehouse][currentWeight] > 0 ){
              enteringWarehouse[warehouse][currentWeight]--;
              //@ assert warehouseCurrentWeight[warehouse] + currentWeight <= MAX_WEIGHT_IN_WAREHOUSE;
              //@ set awakenThreadC = N_WAREHOUSE + warehouse;
              //@ set awakenThreadR = currentWeight;
              signaled++;
          }
        }
      }
    } else { // warehouse > 0
      // exiting could perform iff a robot enter to any warehouse but the first 
      if (exitingWarehouse[warehouse-1] > 0){
        exitingWarehouse[warehouse-1]--;
        //@ set awakenThreadC = warehouse - 1;
        signaled ++;
       //@ assert warehouse - 1 == N_WAREHOUSE -1 || corridor[warehouse-1];
      }
    }
  }

  //@ requires warehouse >= 0 && warehouse < N_WAREHOUSE;
  //derived from POST 
  //@ requires warehouse != N_WAREHOUSE ==> corridor[warehouse]; 
  //@ assignable enteringWarehouse[*]; 
  //@ assignable exitingWarehouse[*];
  //@ diverges false;
  //prop_safe_signal
  /*@ ensures
    @  (\forall int j; j>=0 && j < N_WAREHOUSE;
    @    (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE + 1; 
    @        (enteringWarehouse[j][i] + 1 == \old(enteringWarehouse)[j][i] ==> 
    @                  warehouseCurrentWeight[j] + i <= MAX_WEIGHT_IN_WAREHOUSE)
    @    )
    @  )
    @  &&
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (exitingWarehouse[i] + 1 == \old(exitingWarehouse)[i] 
    @                  ==> ((i != N_WAREHOUSE -1 && corridor[i]) || i == N_WAREHOUSE -1)
    @        )
    @  );
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @  (\forall int j; j>=0 && j < N_WAREHOUSE;
    @    (\forall int i; i>=0 && i < MAX_WEIGHT_IN_WAREHOUSE +1; i != N_WAREHOUSE - awakenThreadC ==>
    @                   (enteringWarehouse[j][i] == 
    @                        \old(enteringWarehouse[j][i]))
    @    )
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @           i != awakenThreadC ==> exitingWarehouse[i] == \old(exitingWarehouse)[i]
    @    )
    @  ) 
    @  && 
    @  ( awakenThreadC != -1 ==> (
    @    ( awakenThreadC > N_WAREHOUSE ==> 
    @        (enteringWarehouse[N_WAREHOUSE - awakenThreadC][awakenThreadR] + 1 
    @          == \old(enteringWarehouse)[N_WAREHOUSE - awakenThreadC][awakenThreadR]))
    @    ||
    @    (awakenThreadC <= N_WAREHOUSE ==> 
    @             exitingWarehouse[awakenThreadC] + 1== \old(exitingWarehouse)[awakenThreadC])
    @    )
    @  )
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @    ( awakenThreadC > N_WAREHOUSE ==> 
    @      enteringWarehouse[N_WAREHOUSE - awakenThreadC][awakenThreadR] + 1 ==
    @           \old(enteringWarehouse[N_WAREHOUSE - awakenThreadC][awakenThreadR])) 
    @  &&
    @    (awakenThreadC <= N_WAREHOUSE ==> 
    @      exitingWarehouse[awakenThreadC] + 1== \old(exitingWarehouse[awakenThreadC])
    @    )
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  ( awakenThreadC != -1 && 
    @      ( awakenThreadC > N_WAREHOUSE ==> 
    @         (\old(enteringWarehouse[N_WAREHOUSE - awakenThreadC][awakenThreadR]) > 0
    @          && warehouseCurrentWeight[N_WAREHOUSE - awakenThreadC] + awakenThreadR <= MAX_WEIGHT_IN_WAREHOUSE
    @         )
    @      ) && 
    @      (awakenThreadC <= N_WAREHOUSE ==>
    @         (\old(exitingWarehouse)[awakenThreadC] > 0 && 
    @           (
    @             (awakenThreadC != N_WAREHOUSE -1 && corridor[awakenThreadC]) ||
    @             (awakenThreadC == N_WAREHOUSE -1)    
    @           )
    @         )
    @      )
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
  private void unblockingCodeExitWarehouse(int warehouse, int weight) {
    signaled = 0;
    //@ set awakenThreadC = -1;
    // unblocking code 
    int wid = (warehouse == 0)?0:warehouse-1;
    int availableWeight = MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[wid];
    if (availableWeight > 0) {
      /*@ loop_invariant 
        @    ((currentWeight >= 1 && currentWeight <= availableWeight) || signaled == 1) && 
        @         (\forall int l; l >= 1 && l < currentWeight ; enteringWarehouse[wid][l] == 0) &&
        @         (awakenThreadC != -1 ==> signaled == 1);
        @ assignable enteringWarehouse[wid][*];
        @ decreases availableWeight - currentWeight;
        @*/  
      for (int currentWeight = 1; currentWeight < availableWeight && signaled == 0; currentWeight++){
        if (enteringWarehouse[wid][currentWeight] > 0 ){
            enteringWarehouse[wid][currentWeight]--;
            //@ assert warehouseCurrentWeight[wid] + currentWeight <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
            signaled ++;
        }
      }
    }
  }     

}