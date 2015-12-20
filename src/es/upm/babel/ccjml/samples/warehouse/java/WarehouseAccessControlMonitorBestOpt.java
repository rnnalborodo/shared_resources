package es.upm.babel.ccjml.samples.warehouse.java;

import java.util.PriorityQueue;

import com.sun.jmx.remote.internal.ArrayQueue;

import es.upm.babel.cclib.Monitor;
import es.upm.babel.cclib.Monitor.Cond;

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

public class WarehouseAccessControlMonitorBestOpt implements WarehouseAccessControl {

  // INNER STATE ATTRIBUTES
  private boolean corridor[];
  private int warehouseCurrentWeight[];
      
  // Monitor & conditions definition
	private Monitor mutex;
	private Cond exitingWarehouse[]; // from warehouse i to corridor i+1
	private PriorityQueue<WeightedCondition> enteringWarehouseZero;
	private WeightedCondition enteringWarehouse[];

	public WarehouseAccessControlMonitorBestOpt() {
	  warehouseCurrentWeight = new int[Robots.N_WAREHOUSE];
    corridor = new boolean[Robots.N_WAREHOUSE-1];
	  
		mutex = new Monitor();
		exitingWarehouse = new Cond[Robots.N_WAREHOUSE-1];
		enteringWarehouse = new WeightedCondition[Robots.N_WAREHOUSE-1];
		enteringWarehouseZero = new PriorityQueue<>(Robots.N_ROBOTS);

//		// At most N_ROBOTS may enter to the warehouse 0
//		for(int i = 0; i < Robots.N_ROBOTS; i++)
//			enteringWarehouseZero[i] = new WeightedCondition(mutex.newCond());
		
		/*
		 * N_WAREHOUSE-1 conditions for entering to warehouse n (n > 0)
		 * N_WAREHOUSE-1 conditions for exiting any warehouse
		 */
		for(int i = 0; i < Robots.N_WAREHOUSE-1; i++) {
			exitingWarehouse[i] = mutex.newCond();
			enteringWarehouse[i] = new WeightedCondition(mutex.newCond());
		}
	}

	public void enterWarehouse(int warehouse, int weight) {
		mutex.enter();
		if (warehouseCurrentWeight[warehouse] + weight > Robots.MAX_WEIGHT_IN_WAREHOUSE) {

			if (warehouse == 0){ // warehouse 0 -> create a new WeightedCond
				WeightedCondition wc = new WeightedCondition(mutex.newCond(), weight);
				wc.getCondition().await();
				enteringWarehouseZero.offer(wc);
			} else { // await in the (condition warehouse - 1)
				enteringWarehouse[warehouse-1].setWeight(weight);
				enteringWarehouse[warehouse-1].getCondition().await();
			}
		}

	  //@ assert warehouseCurrentWeight[warehouse] + weight <= Robots.MAX_WEIGHT_IN_WAREHOUSE;

		//updating the corridor if needed
    if (warehouse != 0)
      corridor[warehouse-1] = false;
		warehouseCurrentWeight[warehouse] += weight;

		// unblocking code 
		if (warehouse ==  0){
		  // if there are pending robots waiting for entering warehouse 0
			for (WeightedCondition wc: enteringWarehouseZero){
				if (wc.getCondition().waiting() > 0 && 
				    wc.getWeight() <=  Robots.MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse]){
					wc.getCondition().signal();
					enteringWarehouseZero.remove(wc);
					//@ assert warehouseCurrentWeight[warehouse] + enteringWarehouseZero[i].getWeight() <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
					break;
				}
			}
		} else { // warehouse n > 0
		  // if there is a robot waiting to exit to a corridor 'warehouse', wake it up
			if (exitingWarehouse[warehouse-1].waiting() > 0)
				exitingWarehouse[warehouse-1].signal();
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
		if (warehouse == 0) {
      for (WeightedCondition wc: enteringWarehouseZero){
        if (wc.getCondition().waiting() > 0 && 
            wc.getWeight() <=  Robots.MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse]){
          wc.getCondition().signal();
          enteringWarehouseZero.remove(wc);
          //@ assert warehouseCurrentWeight[warehouse] + enteringWarehouseZero[i].getWeight() <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
          break;
  			}
			}
		} else { // is there any robot in corridor (warehouse-1)?
			if (enteringWarehouse[warehouse-1].getCondition().waiting() > 0 && 
			    enteringWarehouse[warehouse-1].getWeight() <= Robots.MAX_WEIGHT_IN_WAREHOUSE - warehouseCurrentWeight[warehouse] ) {
				enteringWarehouse[warehouse-1].getCondition().signal();
        //@ assert warehouseCurrentWeight[warehouse-1] + enteringWarehouse[warehouse-1].getWeight() <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
			}
		}
		
		mutex.leave();
	}

}