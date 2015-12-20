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

public class WarehouseAccessControlMonitor implements WarehouseAccessControl {
  
  // INNER STATE ATTRIBUTES
  private boolean corridor[];
  private int warehouseCurrentWeight[];
      
  // Monitor & conditions definition
	private Monitor mutex;
	private Cond enteringWarehouse[][],exitingWarehouse[];

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
		if (warehouseCurrentWeight[warehouse] + weight > Robots.MAX_WEIGHT_IN_WAREHOUSE) {
			enteringWarehouse[warehouse][weight].await();
		}

	  //@ assert warehouseCurrentWeight[warehouse] + weight <= Robots.MAX_WEIGHT_IN_WAREHOUSE;

		//updating the corridor if needed
    if (warehouse != 0)
      corridor[warehouse-1] = false;
		warehouseCurrentWeight[warehouse] += weight;

		// unblocking code
		if (warehouse == 0){
  	  int from = Robots.MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse];
  		for (int currentWeight = from; currentWeight < Robots.MAX_WEIGHT_IN_WAREHOUSE; currentWeight++){
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
		warehouseCurrentWeight[warehouse] -= weight;
		if ( warehouse != Robots.N_WAREHOUSE -1 )
			corridor[warehouse] = true;

		// unblocking code 
		int wid = (warehouse == 0)?0:warehouse-1;
    int from = Robots.MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[wid];
    for (int currentWeight = from; currentWeight < Robots.MAX_WEIGHT_IN_WAREHOUSE; currentWeight++){
      if (enteringWarehouse[wid][currentWeight].waiting() > 0 ){
          enteringWarehouse[wid][currentWeight].signal();
          break;
        //@ assert warehouseCurrentWeight[wid] + currentWeight <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
      }
    }
		
		mutex.leave();
	}

}