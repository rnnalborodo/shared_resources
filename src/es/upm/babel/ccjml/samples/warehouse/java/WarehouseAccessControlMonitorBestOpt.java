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
   * List of weighted conditions for entering to warehouse 0. Robots that
   * are waiting to enter to the warehouse complex. There can be as many as 
   * they want.
   * 
   * The priority is over the weight of the robot that are entering and 
   * can be changed by reimplementing 'compareTo' method of WeightedCondition. 
   */
	private PriorityQueue<WeightedCondition> enteringWarehouseZero;
	
  /** 
   * Array of Robots.N_WAREHOUSE conditions for blocking calls to enterWarehouse 
   * when the warehouse > 0.
   * 
   * This optimization is made due to the fact that only one robot can be 
   * waiting to enter.
   */
	private WeightedCondition enteringWarehouse[];

  /**
   * Conditions for blocking exitWarehouse invocations. The length of the 
   * array is Robots.N_WAREHOUSE.
   */
	private Cond exitingWarehouse[];
	
	public WarehouseAccessControlMonitorBestOpt() {
	  warehouseCurrentWeight = new int[Robots.N_WAREHOUSE];
    corridor = new boolean[Robots.N_WAREHOUSE-1];
	  
		mutex = new Monitor();
		exitingWarehouse = new Cond[Robots.N_WAREHOUSE-1];
		enteringWarehouse = new WeightedCondition[Robots.N_WAREHOUSE-1];
		enteringWarehouseZero = new PriorityQueue<>(Robots.N_ROBOTS);

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
		  // CPRE does not hold, see where to put it
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

    //updating the corridor if we are not exiting the last warehouse
    if (warehouse != 0)
      corridor[warehouse-1] = false;
    
    // updating warehouse current weight
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

		// updating the current weight of the warehouse
    warehouseCurrentWeight[warehouse] -= weight;
    
    // updating the leaving corridor iff the robot enters from a corridor
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