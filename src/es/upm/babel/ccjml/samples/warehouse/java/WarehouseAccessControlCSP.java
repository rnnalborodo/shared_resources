package es.upm.babel.ccjml.samples.warehouse.java;

import org.jcsp.lang.*;

public class WarehouseAccessControlCSP implements WarehouseAccessControl, CSProcess {

  public final int MAX_WEIGHT, N_WAREHOUSES;
  
  // Resource state
  private int weight[]; // # = N_WAREHOUSES
  private boolean occupied[];  // # = N_WAREHOUSES

  /** WRAPPER IMPLEMENTATION */
  // # = N_WAREHOUSES X MAX_WEIGHT
  Any2OneChannel chEnteringWarehouse[][]; 
  // # = N_WAREHOUSES
  Any2OneChannel chExitingWarehouse[];

  public WarehouseAccessControlCSP(int n, int w) {
    this.MAX_WEIGHT = w;
    this.N_WAREHOUSES = n;
    // initialize state and create channels...
    weight = new int[N_WAREHOUSES];
    occupied = new boolean[N_WAREHOUSES];
    // initialize channels
    chEnteringWarehouse = new Any2OneChannel[N_WAREHOUSES][MAX_WEIGHT];
    chExitingWarehouse = new Any2OneChannel[N_WAREHOUSES];
    for (int i = 0; i < chExitingWarehouse.length; i++) {
      chExitingWarehouse[i] = Channel.any2one();
      for (int j = 0; j < chEnteringWarehouse[i].length; j++) {
        chEnteringWarehouse[i][j] = Channel.any2one();
      }
    }
  }
 
  public void enterWarehouse(int n, int w) {
    //@ assume n => 0 && n < N-WAREHOUSE && w > 0;
    chEnteringWarehouse[n][w-1].out().write(
                        new WeightedRequest(n,w));
  }

  public void exitWarehouse(int n, int w) {
    //@ assume n => 0 && n < N-WAREHOUSE && w > 0; 
    chExitingWarehouse[n].out().write(w);
  }

/** SERVER IMPLEMENTATION */
public void run() {
  /* 
   * inputs[0..N_WAREHOUSES] -> exitWarehouse
   * inputs[N_WAREHOUSES..] -> enterWarehouse
   */
  Guard[] inputs = new Guard
      [N_WAREHOUSES + (MAX_WEIGHT * N_WAREHOUSES)];
  for (int n = 0; n < N_WAREHOUSES; n++) {
    inputs[n] = chExitingWarehouse[n].in();
    // flattening enteringWarehouse channels
    for (int w = 0; w < MAX_WEIGHT; w++) {
      inputs[N_WAREHOUSES + n*MAX_WEIGHT+w] = 
                    chEnteringWarehouse[n][w].in();
    }
  }

  Alternative services = new Alternative(inputs);
  int chosenService = 0;

  /** Conditional reception for fairSelect() **/
  boolean[] syncCond = new boolean
      [N_WAREHOUSES + (MAX_WEIGHT * N_WAREHOUSES)];
  while (true) {
    // updating syncCond for enterWarehouse(0,w)
	  for (int n = 0; n < N_WAREHOUSES; n++) {
	    System.out.println(n);
		  //exitWarehouse(n,w) CPRE
	    syncCond[n] = ! 
               (n != N_WAREHOUSES) || !occupied[n];
	    // enterWarehouse(n,w) CPRE
	    for (int w = 0; w < MAX_WEIGHT; w++) {
	      syncCond[N_WAREHOUSES + n*MAX_WEIGHT+w] = 
                   weight[n] + (w+1) <= MAX_WEIGHT;
	    }
	  }
	  
    /*@ assume (\forall int i; i> = 0 i < syncCond.length; 
      @                syncCond[i] ==> channelAssocCpre(i)) &&
      @        syncCond.length == inputs.length;
      @*/

    chosenService = services.fairSelect(syncCond);
    //@ assume chosenService < guards.length && chosenService >= 0;
    //@ assume guards[chosenService].pending() > 0 && syncCond[chosenService];

    if (chosenService < N_WAREHOUSES) { // exit OP
      //@ assert chosenService != N_WAREHOUSES ==> !occupied[chosenService];
      int w = Integer.valueOf((Integer)chExitingWarehouse[chosenService].in().read());
      int n = chosenService;
      weight[n]-= w;
      if (n != N_WAREHOUSES - 1) occupied[n] = true; 
    } else {//chosenService>=N_WAREHOUSES ==> enter
      //@ assert weight[chosenService] + w <= MAX_WEIGHT;
      //reading message containing the weight of robot 
      WeightedRequest req = (WeightedRequest)((AltingChannelInput)inputs[chosenService]).read();
      if (req.getWarehouse() != 0) occupied[req.getWarehouse()-1] = false;
      weight[req.getWarehouse()] += req.getWeight();
    }
  } // end of server loop 
} // end of run method
}
