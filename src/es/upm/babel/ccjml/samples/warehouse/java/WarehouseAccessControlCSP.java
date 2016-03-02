package es.upm.babel.ccjml.samples.warehouse.java;
 
import org.jcsp.lang.*;

public class WarehouseAccessControlCSP implements CSProcess {

  public int MAX_WEIGHT_WAREHOUSE , N_WAREHOUSE;
  
  // Resource state
  private int weight[];
  private boolean occupied[];

  /** WRAPPER IMPLEMENTATION */
  // robots entering to warehouse0 (# channels = MAX_WEIGHT_WAREHOUSE)
  Any2OneChannel chEnteringWarehouse0[];
  // channel to sent robot's weight (# channels = N_WAREHOUSE)
  Any2OneChannel chRobotWeight[];
  Any2OneChannel chEnteringWarehouse[][]; //(# channels = N_WAREHOUSE * MAX_WEIGHT_WAREHOUSE )
  Any2OneChannel chExitingWarehouse[]; //(# channels = N_WAREHOUSE)

  public WarehouseAccessControlCSP() {
    // initialize state and create channels...
  }
 
  public void enterWarehouse(int n, int w) {
    //@ assume n => 0 && n < N-WAREHOUSE && w > 0;
    if (w == 0) 
      chEnteringWarehouse0[w].out().write(w);
    else 
      chEnteringWarehouse[n][w].out().write(w);
  }

  public void exitWarehouse(int n, int w) {
    //@ assume n => 0 && n < N-WAREHOUSE && w > 0; 
    chExitingWarehouse[n].out().write(w);
  }

  /** SERVER IMPLEMENTATION */
  public void run() {
    /* 
     * Channel splitting positions (MAX_WEIGHT_WAREHOUSE + N_WAREHOUSE*2)
     * inputs[0..MAX_WEIGHT_WAREHOUSE] -> chEnteringWarehouse0
     * inputs[MAX_WEIGHT_WAREHOUSE..N_WAREHOUSE] -> exitingWarehouse
     * inputs[MAX_WEIGHT_WAREHOUSE+N_WAREHOUSE.. inputs.length] -> enteringWarehouse
     */
    Guard[] inputs = new Guard[MAX_WEIGHT_WAREHOUSE + N_WAREHOUSE];
    for (int w = 0; w < MAX_WEIGHT_WAREHOUSE; w++) {
      inputs[w] = chEnteringWarehouse0[w].in();
    }
    for (int n = MAX_WEIGHT_WAREHOUSE; n < MAX_WEIGHT_WAREHOUSE + N_WAREHOUSE; n++) {
      inputs[n] = chExitingWarehouse[n - MAX_WEIGHT_WAREHOUSE].in();
      // flattening enteringWarehouse channels
      for (int w = 0; w < MAX_WEIGHT_WAREHOUSE; w++) {
        inputs[n + N_WAREHOUSE +w] = chEnteringWarehouse[n-MAX_WEIGHT_WAREHOUSE][w].in();
      }
    }

    final Alternative services = new Alternative(inputs);
    int chosenService = 0;

    /** Conditional reception for fairSelect() **/
    boolean[] syncCond = new boolean[MAX_WEIGHT_WAREHOUSE + N_WAREHOUSE*2];
    while (true) {
      // updating synchronization conditions array
      // updating syncCond for enterWarehouse(0,w)
	  for (int w = 0; w < MAX_WEIGHT_WAREHOUSE; w++) {
		  syncCond[w] = weight[0] + w <= MAX_WEIGHT_WAREHOUSE;
	  }
	  for (int n = MAX_WEIGHT_WAREHOUSE; n < MAX_WEIGHT_WAREHOUSE + N_WAREHOUSE; n++) {
		// updating syncCond for exitWarehouse(n,w)
	    syncCond[n] = ! (n - MAX_WEIGHT_WAREHOUSE != N_WAREHOUSE) || !occupied[n - MAX_WEIGHT_WAREHOUSE];
	    
	    // updating syncCond for enterWarehouse(n,w)
	    for (int w = 0; w < MAX_WEIGHT_WAREHOUSE; w++) {
	      syncCond[n + N_WAREHOUSE + w] = weight[n-MAX_WEIGHT_WAREHOUSE] + w <= MAX_WEIGHT_WAREHOUSE;
	    }
	  }
      /*@ assume (\forall int i; i> = 0 i < syncCond.length; 
        @                syncCond[i] ==> channelAssocCpre(i)) &&
        @        syncCond.length == inputs.length;
        @*/

      chosenService = services.fairSelect(syncCond);
      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0 && syncCond[chosenService];

      if (chosenService >= 0 && chosenService < MAX_WEIGHT_WAREHOUSE) { 
        //@ assert weight[0] + w <= MAX_WEIGHT_WAREHOUSE;   //enterWarehouse0 CPRE
        //reading message containing the weight of robot
        int w = Integer.valueOf((Integer)chEnteringWarehouse0[chosenService].in().read());
        // updating state -> w == chosenService
        weight[0] += w;  
      } else if (chosenService >= MAX_WEIGHT_WAREHOUSE && chosenService < MAX_WEIGHT_WAREHOUSE + N_WAREHOUSE) { 
        //@ assert weight[n-MAX_WEIGHT_WAREHOUSE] + w <= MAX_WEIGHT_WAREHOUSE; //enterWarehouse CPRE
        int w = Integer.valueOf((Integer)chEnteringWarehouse0[chosenService].in().read());
        int n = chosenService - MAX_WEIGHT_WAREHOUSE;
        if (n != 0) occupied[w-1] = false;
        weight[n] += w;
      } else if (chosenService >= MAX_WEIGHT_WAREHOUSE + N_WAREHOUSE) { 
        //@ assert n - MAX_WEIGHT_WAREHOUSE != N_WAREHOUSE ==> !occupied[n - MAX_WEIGHT_WAREHOUSE] //exitWarehouse
        int w = Integer.valueOf((Integer)chEnteringWarehouse0[chosenService].in().read());
        int n = chosenService - MAX_WEIGHT_WAREHOUSE - N_WAREHOUSE;
        weight[n]-= w;
        if (n != N_WAREHOUSE - 1) occupied[n] = true; 
      }
    }
  }
}
