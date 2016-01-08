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
    @                     &&  (\forall int j;j >=0 && j<= MAX_WEIGHT_IN_WAREHOUSE;
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
  private void dummyUnblockingCode(){
    //@ set awakenThreadC = -1;
    //@ set awakenThreadR = -1;
    signaled = 0;

    /*@ loop_invariant 
      @    ((w >= 1 && w <= N_WAREHOUSE) || signaled == 1) && 
      @         (\forall int l; l >= 1 && l < w ; enteringWarehouse[w][l] == 0) &&
      @         (awakenThreadC != -1 ==> signaled == 1);
      @ assignable enteringWarehouse[*];
      @ decreases N_WAREHOUSE - w;
      @*/    
    // for each warehouse...
    for (int w = 0; w < N_WAREHOUSE && signaled == 0; w++) {
      // and for each possible weight...
      /*@ loop_invariant 
        @    ((j>= 1 && j<= MAX_WEIGHT_IN_WAREHOUSE + 1) || signaled == 1) && 
        @         (\forall int k; k >= 1 && k < j; enteringWarehouse[w][k] == 0) &&
        @         (awakenThreadC != -1 ==> signaled == 1);
        @ assignable enteringWarehouse[*];
        @ decreases MAX_WEIGHT_IN_WAREHOUSE + 1 - j;
        @*/
      for (int j = 0; j < MAX_WEIGHT_IN_WAREHOUSE + 1 && signaled == 0; j++) {
        // we seek for an illegally blocked thread (0 could not be considered)
        if ( warehouseCurrentWeight[w] + j <= MAX_WEIGHT_IN_WAREHOUSE //cpreEnter
            && enteringWarehouse[w][j] > 0) {
          enteringWarehouse[w][j]--;
          //@ set awakenThreadC = N_WAREHOUSE + w;
          //@ set awakenThreadR = j;
          //@ assert warehouseCurrentWeight[w] + j <= MAX_WEIGHT_IN_WAREHOUSE;
          signaled++;
        }
      }
    }
    
    /*@ loop_invariant 
      @    ((i >= 1 && i <= N_WAREHOUSE) || signaled == 1) && 
      @         (\forall int j; j >= 1 && j < i ; enteringWarehouse[i][j] == 0) &&
      @         (awakenThreadC != -1 ==> signaled == 1);
      @ assignable enteringWarehouse[*];
      @ decreases N_WAREHOUSE - i;
      @*/  
    // trying to unblock a robot that wants to leave the warehouse
    // for each warehouse...
    for (int i = 0; i < N_WAREHOUSE && signaled == 0; i++) {
      // we seek for an illegally blocked robot that could exit a warehouse
      if ( (i == N_WAREHOUSE -1 || corridor[i]) && exitingWarehouse[i] > 0) {
        exitingWarehouse[i]--;
        //@ set awakenThreadC = i;
        //@ assert i == N_WAREHOUSE -1 || !corridor[i];
        signaled++;
      }
    }
  }
}