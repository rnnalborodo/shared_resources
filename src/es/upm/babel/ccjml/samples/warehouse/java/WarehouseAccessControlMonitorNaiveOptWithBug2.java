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
 * @author BABEL Group - Technical University of Madrid
 */

public class WarehouseAccessControlMonitorNaiveOptWithBug2 implements WarehouseAccessControl {
  
  // INNER STATE ATTRIBUTES
  /**
   *  which corridor is free. It has the same length that warehouseCurrentWeight
   */
  private boolean corridor[];
  /**
   *  current weight of all warehouses. All values must be equal or less than
   *  Robots.MAX_WEIGHT_IN_WAREHOUSE. 
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
	public WarehouseAccessControlMonitorNaiveOptWithBug2() {
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

		if (warehouse == 0){
  	  int from = Robots.MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse];
  	  // BUG: instead of decrementing the control variable, we incremented
  	  // correctness
  		for (int currentWeight = Robots.MAX_WEIGHT_IN_WAREHOUSE; currentWeight >= 0; currentWeight--){
  			if (enteringWarehouse[warehouse][currentWeight].waiting() > 0 ){
  				  enteringWarehouse[warehouse][currentWeight].signal();
  			    //@ assert warehouseCurrentWeight[warehouse] + currentWeight <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
  				  break;
  			}
  		}
		} else { // exiting could perform iff a robot enter to any warehouse but the first 
			if (exitingWarehouse[warehouse-1].waiting() > 0){
				exitingWarehouse[warehouse-1].signal();
		   //@ assert warehouse != Robots.N_WAREHOUSE -1 && corridor[warehouse-1];
			}
		}

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
		int wid = (warehouse == 0)?0:warehouse-1;
    int from = Robots.MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[wid];
    for (int currentWeight = from; currentWeight >= 0; currentWeight--){
      if (enteringWarehouse[wid][currentWeight].waiting() > 0 ){
          enteringWarehouse[wid][currentWeight].signal();
          break;
        //@ assert warehouseCurrentWeight[wid] + currentWeight <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
      }
    }
		
		mutex.leave();
	}

}