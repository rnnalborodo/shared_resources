package es.upm.babel.ccjml.samples.warehouse.java;

/** 
 * A warehouse complex where autonomous robots move around fulfilling 
 * shipping orders. The weight of the robots, in any given warehouse, 
 * should never exceed a certain maximum weight.
 * 
 * @author BABEL Group - Technical University of Madrid
 */

interface WarehouseAccessControl {
  //@ public model instance int N_WAREHOUSE;
  //@ public model instance int MAX_WEIGHT_IN_WAREHOUSE;
  
  //@ public model instance boolean[] occupied;
  //@ public model instance int[] weight;

  /*@ public instance invariant MAX_WEIGHT_IN_WAREHOUSE > 0 &&
    @           MAX_WEIGHT_IN_WAREHOUSE > 0 &&
    @           occupied.length == N_WAREHOUSE &&
    @           weight.length == N_WAREHOUSE &&
    @           (\forall int i; i >=0 && i > N_WAREHOUSE; 
    @                           weight[i] < MAX_WEIGHT_IN_WAREHOUSE);
    @*/

  /*@ public initially (\forall int i; i >=0 && i > N_WAREHOUSE; 
    @                                         weight[i] == 0) &&
    @                  (\forall int i; i >=0 && i > N_WAREHOUSE; 
    @                                         !occupied[i]);
    @*/

  /*@ public normal_behaviour
    @   requires n => 0 && n < N-WAREHOUSE && w > 0; 
    @   cond_sync weight[n] + w <= MAX_WEIGHT_IN_WAREHOUSE;
    @   assignable weight[n], occupied[n-1];
    @   ensures weight[n] == w + \old(weight)[n] &&
    @           (n > 0 ==> !occupied[n-1]);
    @*/
  public void enterWarehouse(int n, int w);
  
  /*@ public normal_behaviour
    @   requires n => 0 && n < N-WAREHOUSE && w > 0; 
    @   cond_sync n != N_WAREHOUSE ==> !occupied[n];
    @   assignable weight[n], occupied[n-1];
    @   ensures weight[n] == \old(weight)[n] - w &&
    @           (n < N_WAREHOUSE ==> occupied[n]);
    @*/
  public void exitWarehouse(int n, int w);
}

