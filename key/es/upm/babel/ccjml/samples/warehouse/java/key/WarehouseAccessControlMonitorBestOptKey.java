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

  public static final int N_ROBOTS = 2;
  public static final int N_WAREHOUSE = 4;
  public static final int MAX_WEIGHT_IN_WAREHOUSE = 100;
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
  //@ public invariant (\forall int i; i >=0 && i<= N_WAREHOUSE; exitingWarehouse[i] >= 0);     
  private /*@ spec_public @*/ int exitingWarehouse[];
  
  //@ public invariant enteringWarehouseZero.length == N_ROBOTS;  
	private /*@ spec_public @*/ WeightedCondition enteringWarehouseZero[];
	
  //@ public invariant enteringWarehouse.length == N_WAREHOUSE;  
	private /*@ spec_public @*/ WeightedCondition enteringWarehouse[];

  //@ public invariant signaled == 0 || signaled == 1;
  private /*@ spec_public @*/ int signaled;

	//@ requires warehouse >=0 && warehouse <= N_WAREHOUSE;
  //@ requires weight >=0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;
  //@ requires warehouse == 0 || !corridor[warehouse-1] ; // VER!!! split? lazy
  //@ assignable exitingWarehouse[((warehouse == 0)?0:warehouse-1)];
  //@ assignable enteringWarehouseZero[*];
  //@ diverges false;
    //prop_safe_signal
  /*@ ensures
    @  (\forall int i; i>=0 && i < N_ROBOTS; 
    @        (enteringWarehouseZero[i].getCondition() + 1 == \old(enteringWarehouse[i]).getCondition() ==> 
    @                  warehouseCurrentWeight[0] + i <= MAX_WEIGHT_IN_WAREHOUSE))
    @  &&
    @  (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @        (exitingWarehouse[i] + 1 == \old(exitingWarehouse)[i] 
    @                  ==> i+1 != N_WAREHOUSE -1 && corridor[i])
    @  );
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @    (\forall int i; i>=0 && i < N_ROBOTS; i != N_WAREHOUSE - awakenThread ==>
    @                   (enteringWarehouseZero[i].getCondition() == 
    @                        \old(enteringWarehouseZero[i]).getCondition())
    @    )
    @    &&
    @    (\forall int i; i>=0 && i < N_WAREHOUSE; 
    @                   exitingWarehouse[i] == \old(exitingWarehouse)[i]
    @    ) 
    @  && 
    @  ( awakenThread != -1 ==> (
    @    ( awakenThread > N_WAREHOUSE ==> 
    @        (enteringWarehouseZero[N_WAREHOUSE - awakenThread].getCondition() + 1 
    @          == \old(enteringWarehouse[N_WAREHOUSE - awakenThread]).getCondition())
    @    ) ||
    @    (awakenThread <= N_WAREHOUSE ==> exitingWarehouse[awakenThread] + 1
    @                                   == \old(exitingWarehouse)[awakenThread])
    @    )
    @  )
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @     enteringWarehouseZero[N_WAREHOUSE - awakenThread].getCondition() + 1 ==
    @           \old(enteringWarehouseZero[N_WAREHOUSE - awakenThread]).getCondition() ||
    @     exitingWarehouse[awakenThread] + 1== \old(exitingWarehouse)[awakenThread]
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  ( awakenThread != -1 && 
    @      (awakenThread > N_WAREHOUSE ==> 
    @         (\old(enteringWarehouseZero[N_WAREHOUSE - awakenThread]).getCondition() > 0
    @         && warehouseCurrentWeight[0] + enteringWarehouseZero[N_WAREHOUSE - awakenThread].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE)
    @      ) && 
    @      (awakenThread <= N_WAREHOUSE ==>
    @         (\old(exitingWarehouse)[awakenThread] > 0 && 
    @                 awakenThread + 1 != N_WAREHOUSE -1 && corridor[awakenThread])
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
		  // if there are pending robots waiting for entering warehouse 0
      for (int i =0; i<= enteringWarehouseZero.length; i++){
        if (enteringWarehouseZero[i].getCondition() > 0 && 
            enteringWarehouseZero[i].getWeight() <=  MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse]){
          enteringWarehouseZero[i].signalCondition();
          //@ assert warehouseCurrentWeight[warehouse] + enteringWarehouseZero[i].getWeight() <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
          signaled ++;
          //@set awakenThread = N_WAREHOUSE + i;
          break;
        }
			}
		} else { // warehouse n > 0
		  // if there is a robot waiting to exit to a corridor 'warehouse', wake it up
			if (exitingWarehouse[warehouse-1] > 0)
				exitingWarehouse[warehouse-1]--;
        signaled ++;
        //@set awakenThread = warehouse -1;

		}
	}
	
	//@ requires warehouse >=0 && warehouse <= N_WAREHOUSE;
  //@ requires weight >=0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;
  //@ assignable enteringWarehouse[((warehouse == 0)?0:warehouse-1)];
	//@ assignable enteringWarehouseZero[*];
  //@ diverges false;
	public void unblockingCodeExitWarehouse(int warehouse, int weight) {
		// unblocking code 
    signaled = 0;
    //@ set awakenThread = -1;
		if (warehouse == 0) {
      for (int i =0; i<= enteringWarehouseZero.length; i++){
        if (enteringWarehouseZero[i].getCondition() > 0 && 
            enteringWarehouseZero[i].getWeight() <=  MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse]){
          enteringWarehouseZero[i].signalCondition();
          //@ assert warehouseCurrentWeight[warehouse] + enteringWarehouseZero[i].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE;
          break;
  			}
			}
		} else { // is there any robot in corridor (warehouse-1)?
			if (enteringWarehouse[warehouse-1].getCondition() > 0 && 
			    enteringWarehouse[warehouse-1].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse] ) {
				enteringWarehouse[warehouse-1].signalCondition();
        //@ assert warehouseCurrentWeight[warehouse-1] + enteringWarehouse[warehouse-1].getWeight() <= MAX_WEIGHT_IN_WAREHOUSE;
			}
		}
	}

	//@ requires warehouse >=0 && warehouse <= N_WAREHOUSE;
  //@ requires weight >=0 && weight <= MAX_WEIGHT_IN_WAREHOUSE;
  //@ assignable enteringWarehouse[((warehouse == 0)?0:warehouse-1)];
  //@ assignable enteringWarehouseZero[*];
  //@ diverges false;
  public void _unblockingCodeExitWarehouse(int warehouse, int weight) {
    
  }

}