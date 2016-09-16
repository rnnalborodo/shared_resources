package es.upm.babel.ccjml.samples.warehouse.java;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

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

public class WarehouseAccessControlMonitorClient implements WarehouseAccessControl {
  
  // INNER STATE ATTRIBUTES
  /**
   *  Describes which corridor is free. It has the same length that 
   *  warehouseCurrentWeight
   *  
   *  true -> a robot is present
   */
  private boolean occupied[];
  /**
   *  Represents the current weight of all warehouses. All values must be 
   *  equal or less than Robots.MAX_WEIGHT_IN_WAREHOUSE.
   *  
   *    warehouse0 is follow by corridor 0
   *    w0 - c0 - w1 - c1 - w2
   */
  private int weight[];
      
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
   * Conditions for blocking exitWarehouse invocations.
   */
  private Map<Monitor.Cond, Integer> conditionsExiting;

  /** 
   * constructor
   */
	public WarehouseAccessControlMonitorClient() {
	  // initilizing the inner state of the shared resource
	  weight = new int[Robots.N_WAREHOUSE];
    occupied = new boolean[Robots.N_WAREHOUSE-1];
	  
    // initilizing synchronization mechanism
		mutex = new Monitor();
		
		/* enteringWarehouse -> column 0 is unused because a weight must be 
		 * positive - this is a direct implementation without any optimization
		 */
		enteringWarehouse = new Cond[Robots.N_WAREHOUSE][Robots.MAX_WEIGHT_IN_WAREHOUSE+1];
		
		conditionsExiting = new HashMap<>();
		
    for(int i = 0; i < Robots.N_WAREHOUSE; i++){
      for(int j = 0; j < Robots.MAX_WEIGHT_IN_WAREHOUSE + 1; j++){
        enteringWarehouse[i][j] = mutex.newCond();
      }
    }
		
	}

	public void enterWarehouse(int n, int w) {
		mutex.enter();
		// only enter those robots that does not exceed maximum weight
		if (weight[n] + w > Robots.MAX_WEIGHT_IN_WAREHOUSE) {
			enteringWarehouse[n][w].await();
		}
		
	  //@ assert warehouseCurrentWeight[warehouse] + weight <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
		
		//updating the corridor if we are not exiting the last warehouse
    if (n != 0)
      occupied[n-1] = false;
    // updating warehouse current weight
		weight[n] += w;

		// unblocking code
		dummyUnblockingCode();

		mutex.leave();
	}
	
	public void exitWarehouse(int n, int w) {
		mutex.enter();

		if (n != Robots.N_WAREHOUSE -1 && occupied[n]) {
		  Monitor.Cond cond = mutex.newCond();

		  conditionsExiting.put(cond, n);
      cond.await();
		} 

		//@ assert warehouse == Robots.N_WAREHOUSE -1 || !corridor[warehouse];
		
		// updating the current weight of the warehouse
		weight[n] -= w;
		
		// updating the leaving corridor iff the robot exits any inner warehouse
		if ( n != Robots.N_WAREHOUSE -1 )
			occupied[n] = true;

    // unblocking code
    dummyUnblockingCode();
		
		mutex.leave();
	}

	// unblocking code
	
	private void dummyUnblockingCode(){
    int signaled = 0;
    
    // for each warehouse...
    for (int i = 0; i < Robots.N_WAREHOUSE && signaled == 0; i++) {
      // and for each possible weight...
      for (int j = 0; j < Robots.MAX_WEIGHT_IN_WAREHOUSE + 1 && signaled == 0; j++) {
        // we seek for an illegally blocked thread (0 could not be considered)
        if ( weight[i] + j <= Robots.MAX_WEIGHT_IN_WAREHOUSE //cpreEnter
            && enteringWarehouse[i][j].waiting() > 0) {
          enteringWarehouse[i][j].signal();
          //@ assert warehouseCurrentWeight[i] + j <= Robots.MAX_WEIGHT_IN_WAREHOUSE;
          signaled++;
        }
      }
    }
    
    // trying to unblock a robot that wants to leave the warehouse
    // for each warehouse...
    for(Entry<Monitor.Cond, Integer> entry: conditionsExiting.entrySet()){
      if ( (entry.getValue() == Robots.N_WAREHOUSE -1 || occupied[entry.getValue()])) {
        conditionsExiting.remove(entry.getKey());
        entry.getKey().signal();
        //@ assert entry.getValue() == Robots.N_WAREHOUSE -1 || !corridor[entry.getValue()];
        signaled++;
        break;
      }
    }
  }

}