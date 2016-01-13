package es.upm.babel.ccjml.samples.warehouse.java.key;

/** 
 * WarehouseAccessControl implementation using Babel Priority Monitors.
 * 
 * Thread indexation for robots entering to warehouse 0.
 * Parameter indexation for entering warehouse n > 0.
 * 
 * Parameter indexation for leaving a warehouse n.
 * 
 * @author BABEL Group - Technical University of Madrid
 */

public class WarehouseAccessControlMonitorBestOptKey {

  //@ ghost int awakenThread;

  //@ public invariant N_ROBOTS > 0;
  public static final int N_ROBOTS = 2;
  //@ public invariant N_WAREHOUSE > 0;
  public static final int N_WAREHOUSE = 2;
  //@ public invariant MAX_WEIGHT_IN_WAREHOUSE > 0;
  public static final int MAX_WEIGHT_IN_WAREHOUSE = 5;
  
  // INNER STATE ATTRIBUTES
  //@ public invariant corridor.length == N_WAREHOUSE -1;
  private /*@ spec_public @*/ boolean corridor[];
  
  /*@ public invariant (\forall int i; i >=0 && i< N_WAREHOUSE; 
    @                            warehouseCurrentWeight[i] >= 0 && 
    @                            warehouseCurrentWeight[i] <= MAX_WEIGHT_IN_WAREHOUSE)
    @                  && warehouseCurrentWeight.length == N_WAREHOUSE;
    @*/
  private /*@ spec_public @*/int warehouseCurrentWeight[];
      
  // Monitor & conditions definition
  /*@ public invariant (\forall int i; i >=0 && i< N_WAREHOUSE;
    @                                        exitingWarehouse[i] >= 0)
    @                  && exitingWarehouse.length == N_WAREHOUSE;
    @*/
  private /*@ spec_public @*/ int exitingWarehouse[];
  
  /*@
    @ public invariant enteringWarehouseZero.length == N_ROBOTS && 
    @   (\forall int i; i >= 0 && i < N_ROBOTS -1;
    @              enteringWarehouseZero[i]!= null && 
    @              enteringWarehouseZero[i].getWeight() > 0 &&
    @              enteringWarehouseZero[i].getWeight() <= enteringWarehouseZero[i+1].getWeight() )
    @ ;
    @*/
  private /*@ spec_public @*/ WeightedCondition enteringWarehouseZero[];
  
  /*@ public invariant enteringWarehouse.length == N_WAREHOUSE &&
    @              (\forall int i; i >= 1 && i < N_WAREHOUSE;
    @                                    enteringWarehouse[i]!= null);
    @*/
  private /*@ spec_public @*/ WeightedCondition enteringWarehouse[];

  //@ public invariant signaled == 0 || signaled == 1;
  private /*@ spec_public @*/ int signaled;

  //@ requires warehouse >=0 && warehouse <= N_WAREHOUSE;
  //@ requires weight >=0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;
  //@ requires warehouse > 0 ==> corridor[warehouse-1] ;
  //@ assignable exitingWarehouse[*];
  //@ assignable enteringWarehouseZero[*];
  //@ assignable enteringWarehouse[*];
  //@ diverges false;
  //prop_safe_signal
  /*@ ensures
    @  (\forall int i; i>=0 && i < N_ROBOTS; 
    @        (enteringWarehouseZero[i].getCondition() + 1 == \old(enteringWarehouseZero[i]).getCondition() ==> 
    @                  warehouseCurrentWeight[i] + enteringWarehouseZero[i].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE))
    @  &&
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (enteringWarehouse[i].getCondition() + 1 == \old(enteringWarehouse[i]).getCondition() ==> 
    @                  warehouseCurrentWeight[i] + enteringWarehouse[i].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE))
    @  &&
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (exitingWarehouse[i] + 1 == \old(exitingWarehouse[i])
    @                  ==> i+1 != N_WAREHOUSE -1 && corridor[i])
    @  );
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @    (\forall int i; i>=0 && i < N_ROBOTS; i != awakenThread ==>
    @                   (enteringWarehouseZero[i].getCondition() == 
    @                        \old(enteringWarehouseZero[i]).getCondition())
    @    )
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; i != N_WAREHOUSE - awakenThread ==>
    @                   (enteringWarehouse[i].getCondition() == 
    @                        \old(enteringWarehouse[i]).getCondition())
    @    )
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; i != N_WAREHOUSE*2 - awakenThread ==>
    @                   exitingWarehouse[i] == \old(exitingWarehouse[i])
    @    ) 
    @  && 
    @  ( awakenThread != -1 ==> (
    @    (awakenThread > 2 * N_WAREHOUSE ==> exitingWarehouse[2 * N_WAREHOUSE - awakenThread] + 1
    @                                   == \old(exitingWarehouse)[2 * N_WAREHOUSE - awakenThread])
    @    ) ||
    @    ( awakenThread > N_WAREHOUSE ==> 
    @        (enteringWarehouse[N_WAREHOUSE - awakenThread].getCondition() + 1 
    @          == \old(enteringWarehouse[N_WAREHOUSE - awakenThread]).getCondition())
    @    ) ||
    @    ( awakenThread <= N_WAREHOUSE ==> 
    @        (enteringWarehouseZero[awakenThread].getCondition() + 1 
    @          == \old(enteringWarehouse[awakenThread]).getCondition())
    @    )
    @  )
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @     enteringWarehouseZero[awakenThread].getCondition() + 1 ==
    @           \old(enteringWarehouseZero[awakenThread]).getCondition() ||
    @     enteringWarehouse[N_WAREHOUSE - awakenThread].getCondition() + 1 ==
    @           \old(enteringWarehouse[N_WAREHOUSE - awakenThread]).getCondition() ||
    @     exitingWarehouse[2*N_WAREHOUSE - awakenThread] + 1== \old(exitingWarehouse[2*N_WAREHOUSE - awakenThread])
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  ( awakenThread != -1 && 
    @      (awakenThread > 2*N_WAREHOUSE ==> 
    @         (\old(exitingWarehouse)[2*N_WAREHOUSE - awakenThread] > 0 && 
    @                 2*N_WAREHOUSE - awakenThread + 1 != N_WAREHOUSE -1 && corridor[2*N_WAREHOUSE - awakenThread])
    @      ) && 
    @      (awakenThread > N_WAREHOUSE ==> 
    @         (\old(enteringWarehouse[N_WAREHOUSE - awakenThread]).getCondition() > 0
    @         && warehouseCurrentWeight[N_WAREHOUSE - awakenThread] + enteringWarehouse[N_WAREHOUSE - awakenThread].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE)
    @      ) && 
    @      (awakenThread <= N_WAREHOUSE ==>
    @         (\old(enteringWarehouseZero[awakenThread]).getCondition() > 0
    @         && warehouseCurrentWeight[awakenThread] + enteringWarehouseZero[awakenThread].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE)
    @      )
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
  public void unblockingEnterWarehouse(int warehouse, int weight) {
    // unblocking code 
    signaled = 0;
    //@ set awakenThread = -1;
    if (warehouse ==  0){
      /*@ loop_invariant 
        @    ((i>= 1 && i<= enteringWarehouseZero.length + 1) || signaled == 1) && 
        @         (\forall int k; k >= 1 && k < i; signaled == 0 ==> enteringWarehouseZero[k].getCondition() == 0) &&
        @         (awakenThread != -1 ==> signaled == 1);
        @ assignable enteringWarehouseZero[*];
        @ decreases enteringWarehouseZero.length + 1 - i;
        @*/
      // if there are pending robots waiting for entering warehouse 0
      for (int i =0; i< enteringWarehouseZero.length && signaled == 0; i++){
        if (enteringWarehouseZero[i].getCondition() > 0 && 
            enteringWarehouseZero[i].getWeight() <=  MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse]){
          enteringWarehouseZero[i].signalCondition();
          //@ assert warehouseCurrentWeight[warehouse] + enteringWarehouseZero[i].getWeight() <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
          signaled ++;
          //@set awakenThread = i;
        }
      }
    } else { // warehouse n > 0
      // if there is a robot waiting to exit to a corridor 'warehouse', wake it up
      if (exitingWarehouse[warehouse-1] > 0){
        exitingWarehouse[warehouse-1]--;
        signaled ++;
        //@set awakenThread = N_WAREHOUSE * warehouse -1;
      }
    }
  }
  
  //@ requires warehouse >=0 && warehouse <= N_WAREHOUSE;
  //@ requires weight >=0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;
  //@ requires warehouse > 0 ==> corridor[warehouse]; // derived from POST
  //@ assignable enteringWarehouse[((warehouse == 0)?0:warehouse-1)];
  //@ assignable enteringWarehouseZero[*];
  //@ diverges false;
  //@ assignable exitingWarehouse[*];
  //@ assignable enteringWarehouseZero[*];
  //@ assignable enteringWarehouse[*];
  //prop_safe_signal
  /*@ ensures
    @  (\forall int i; i>=0 && i < N_ROBOTS; 
    @        (enteringWarehouseZero[i].getCondition() + 1 == \old(enteringWarehouseZero[i]).getCondition() ==> 
    @                  warehouseCurrentWeight[i] + enteringWarehouseZero[i].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE))
    @  &&
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (enteringWarehouse[i].getCondition() + 1 == \old(enteringWarehouse[i]).getCondition() ==> 
    @                  warehouseCurrentWeight[i] + enteringWarehouse[i].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE))
    @  &&
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (exitingWarehouse[i] + 1 == \old(exitingWarehouse[i])
    @                  ==> i+1 != N_WAREHOUSE -1 && corridor[i])
    @  );
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @    (\forall int i; i>=0 && i < N_ROBOTS; i != awakenThread ==>
    @                   (enteringWarehouseZero[i].getCondition() == 
    @                        \old(enteringWarehouseZero[i]).getCondition())
    @    )
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; i != N_WAREHOUSE - awakenThread ==>
    @                   (enteringWarehouse[i].getCondition() == 
    @                        \old(enteringWarehouse[i]).getCondition())
    @    )
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; i != N_WAREHOUSE*2 - awakenThread ==>
    @                   exitingWarehouse[i] == \old(exitingWarehouse[i])
    @    ) 
    @  && 
    @  ( awakenThread != -1 ==> (
    @    (awakenThread > 2 * N_WAREHOUSE ==> exitingWarehouse[2 * N_WAREHOUSE - awakenThread] + 1
    @                                   == \old(exitingWarehouse)[2 * N_WAREHOUSE - awakenThread])
    @    ) ||
    @    ( awakenThread > N_WAREHOUSE ==> 
    @        (enteringWarehouse[N_WAREHOUSE - awakenThread].getCondition() + 1 
    @          == \old(enteringWarehouse[N_WAREHOUSE - awakenThread]).getCondition())
    @    ) ||
    @    ( awakenThread <= N_WAREHOUSE ==> 
    @        (enteringWarehouseZero[awakenThread].getCondition() + 1 
    @          == \old(enteringWarehouse[awakenThread]).getCondition())
    @    )
    @  )
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @     enteringWarehouseZero[awakenThread].getCondition() + 1 ==
    @           \old(enteringWarehouseZero[awakenThread]).getCondition() ||
    @     enteringWarehouse[N_WAREHOUSE - awakenThread].getCondition() + 1 ==
    @           \old(enteringWarehouse[N_WAREHOUSE - awakenThread]).getCondition() ||
    @     exitingWarehouse[2*N_WAREHOUSE - awakenThread] + 1== \old(exitingWarehouse[2*N_WAREHOUSE - awakenThread])
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  ( awakenThread != -1 && 
    @      (awakenThread > 2*N_WAREHOUSE ==> 
    @         (\old(exitingWarehouse)[2*N_WAREHOUSE - awakenThread] > 0 && 
    @                 2*N_WAREHOUSE - awakenThread + 1 != N_WAREHOUSE -1 && corridor[2*N_WAREHOUSE - awakenThread])
    @      ) && 
    @      (awakenThread > N_WAREHOUSE ==> 
    @         (\old(enteringWarehouse[N_WAREHOUSE - awakenThread]).getCondition() > 0
    @         && warehouseCurrentWeight[N_WAREHOUSE - awakenThread] + enteringWarehouse[N_WAREHOUSE - awakenThread].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE)
    @      ) && 
    @      (awakenThread <= N_WAREHOUSE ==>
    @         (\old(enteringWarehouseZero[awakenThread]).getCondition() > 0
    @         && warehouseCurrentWeight[awakenThread] + enteringWarehouseZero[awakenThread].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE)
    @      )
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
  public void unblockingCodeExitWarehouse(int warehouse, int weight) {
    // unblocking code 
    signaled = 0;
    //@ set awakenThread = -1;
    if (warehouse == 0) {
      /*@ loop_invariant 
        @    ((i>= 1 && i<= enteringWarehouseZero.length + 1) || signaled == 1) && 
        @         (\forall int k; k >= 1 && k < i; signaled == 0 ==> enteringWarehouseZero[k].getCondition() == 0) &&
        @         (awakenThread != -1 ==> signaled == 1);
        @ assignable enteringWarehouseZero[*];
        @ decreases enteringWarehouseZero.length + 1 - i;
        @*/
      for (int i =0; i < enteringWarehouseZero.length && signaled == 0; i++){
        if (enteringWarehouseZero[i].getCondition() > 0 && 
            enteringWarehouseZero[i].getWeight() <=  MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse]){
          enteringWarehouseZero[i].signalCondition();
          //@ assert warehouseCurrentWeight[warehouse] + enteringWarehouseZero[i].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE;
          //@ set awakenThread = i;
          signaled++;
        } else if (enteringWarehouseZero[i].getWeight() >  MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse]){
          break;
        }
      }
    } else { // is there any robot in corridor (warehouse-1)?
      if (enteringWarehouse[warehouse-1].getCondition() > 0 && 
          enteringWarehouse[warehouse-1].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse] ) {
        enteringWarehouse[warehouse-1].signalCondition();
        //@ assert warehouseCurrentWeight[warehouse] + enteringWarehouse[warehouse -1].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE;
        //@ set awakenThread = N_WAREHOUSE + warehouse-1;
        signaled++; 
      }
    }
  }
}