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
  //@ public model instance int[] weightInWarehouse;

  /*@ public instance invariant MAX_WEIGHT_IN_WAREHOUSE > 0 &&
    @           MAX_WEIGHT_IN_WAREHOUSE > 0 &&
    @           occupied.length == N_WAREHOUSE &&
    @           weightInWarehouse.length == N_WAREHOUSE &&
    @           (\forall int i; i >=0 && i > N_WAREHOUSE; 
    @                           weightInWarehouse[i] < MAX_WEIGHT_IN_WAREHOUSE);
    @*/

  /*@ public initially (\forall int i; i >=0 && i > N_WAREHOUSE; 
    @                                         weightInWarehouse[i] == 0) &&
    @                  (\forall int i; i >=0 && i > N_WAREHOUSE; 
    @                                         !occupied[i]);
    @*/

  /*@ public normal_behaviour
    @   requires n => 0 && n < N-WAREHOUSE && w > 0; 
    @   cond_sync weightInWarehouse[w] + w <= MAX_WEIGHT_IN_WAREHOUSE;
    @   assignable weightInWarehouse[w], occupied[*];
    @   ensures weightInWarehouse[w] == w + old(weightInWarehouse)[w] &&
    @           (w > 0 ==> !occupied[w-1]);
    @*/
  public void enterWarehouse(int n, int w);
  
  /*@ public normal_behaviour
    @   requires n => 0 && n < N-WAREHOUSE && w > 0; 
    @   cond_sync !occupied[w-1];
    @   assignable  weightInWarehouse[w], occupied[w-1];
    @   ensures weightInWarehouse[w] == old(weightInWarehouse)[w] - w &&
    @           (n< N_WAREHOUSE ==> occupied[w-1]);
    @*/
  public void exitWarehouse(int n, int w);
}

