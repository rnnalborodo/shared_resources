package es.upm.babel.ccjml.samples.warehouse.java;

import es.upm.babel.cclib.Monitor;
import es.upm.babel.cclib.Monitor.Cond;

/** 
 * WarehouseAccessControl implementation using Babel Priority Monitors.
 * 
 * Naive implementation
 * Parameter indexation for robots entering to warehouse.
 * Parameter indexation for leaving a warehouse n.
 * 
 * Unblocking code naive iterating over all conditions 
 * 
 * @author BABEL Group - Technical University of Madrid
 */

public class WarehouseAccessControlMonitor implements WarehouseAccessControl {
  
  // INNER STATE ATTRIBUTES
  /**
   *  Describes which corridor is free. It has the same length that 
   *  warehouseCurrentWeight
   */
  private boolean corridor[];
  /**
   *  Represents the current weight of all warehouses. All values must be 
   *  equal or less than Robots.MAX_WEIGHT_IN_WAREHOUSE. 
   */
  private int warehouseCurrentWeight[];
      
  // MONITOR AND CONDITIONS
  private Monitor mutex;
  
  /** 
   * Robots.N_WAREHOUSE * Robots.MAX_WEIGHT_IN_WAREHOUSE matrix of
   * conditions for blocking calls to enterWarehouse 
   * 
   * enterWarehouse(n,w) will be blocked in enteringWarehouse[n][w]
   */
  private Cond enteringWarehouse[][];
  
  /**
   * Conditions for blocking exitWarehouse invocations. The length of the 
   * array is Robots.N_WAREHOUSE.
   */
  private Cond exitingWarehouse[];

  /** 
   * constructor
   */
	public WarehouseAccessControlMonitor() {
	  warehouseCurrentWeight = new int[Robots.N_WAREHOUSE];
    corridor = new boolean[Robots.N_WAREHOUSE-1];
	  
		mutex = new Monitor();
		enteringWarehouse = new Cond[Robots.N_WAREHOUSE-1][Robots.MAX_WEIGHT_IN_WAREHOUSE -1];
		exitingWarehouse = new Cond[Robots.N_WAREHOUSE-1];

		for(int i = 0; i < Robots.N_WAREHOUSE; i++){
		  for(int j = 0; j < Robots.MAX_WEIGHT_IN_WAREHOUSE; j++){
		    enteringWarehouse[i][j] = mutex.newCond();
		  }
		  exitingWarehouse[i] = mutex.newCond();
		}
	}

	public void enterWarehouse(int warehouse, int weight) {
		mutex.enter();
		// only enter those robots that does not exceed maximum weight
		if (warehouseCurrentWeight[warehouse] + weight > Robots.MAX_WEIGHT_IN_WAREHOUSE) {
			enteringWarehouse[warehouse][weight].await();
		}
		
	  //@ assert warehouseCurrentWeight[warehouse] + weight <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
		
		//updating the corridor if we are not exiting the last warehouse
    if (warehouse != 0)
      corridor[warehouse-1] = false;
    // updating warehouse current weight
		warehouseCurrentWeight[warehouse] += weight;

		// unblocking code
		dummyUnblockingCode();

		mutex.leave();
	}
	
	public void exitWarehouse(int warehouse, int weight) {
		mutex.enter();

		if (warehouse != Robots.N_WAREHOUSE -1 && corridor[warehouse]) 	
			exitingWarehouse[warehouse].await(); 

		//@ assert warehouse != Robots.N_WAREHOUSE -1 && corridor[warehouse];
		
		// updating the current weight of the warehouse
		warehouseCurrentWeight[warehouse] -= weight;
		
		// updating the leaving corridor iff the robot enters from a corridor
		if ( warehouse != Robots.N_WAREHOUSE -1 )
			corridor[warehouse] = true;

    // unblocking code
    dummyUnblockingCode();
		
		mutex.leave();
	}

	// unblocking code
	
	private void dummyUnblockingCode(){
    int signaled = 0;
    for (int i = 0; i < Robots.N_WAREHOUSE && signaled == 0; i++) {
      for (int j = 0; j < Robots.MAX_WEIGHT_IN_WAREHOUSE && signaled == 0; j++) {
        if ( warehouseCurrentWeight[i] + j <= Robots.MAX_WEIGHT_IN_WAREHOUSE //cpreEnter
            && enteringWarehouse[i][j].waiting() > 0) {
          enteringWarehouse[i][j].signal();
          //@ assert warehouseCurrentWeight[i] + j <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
          signaled++;
        }
      }
    }
    for (int i = 0; i < Robots.N_WAREHOUSE && signaled == 0; i++) {
      if (i != Robots.N_WAREHOUSE -1 && corridor[i-1] //cpreExit
          && exitingWarehouse[i].waiting() > 0) {
        exitingWarehouse[i].signal();
        //@ assert i != Robots.N_WAREHOUSE -1 && corridor[i-1];
        signaled++;
      }
    }
  }

}