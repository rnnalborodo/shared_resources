package es.upm.babel.ccjml.samples.warehouse.java;

/** 
 * A warehouse complex where autonomous robots move around fulfilling 
 * shipping orders. The weight of the robots, in any given warehouse, 
 * should never exceed a certain maximum weight.
 * 
 * @author BABEL Group - Technical University of Madrid
 */

public interface WarehouseAccessControl {
  //@ public model instance int N_WAREHOUSES;
  //@ public model instance int MAX_WEIGHT;
  
  //@ public model instance boolean[] occupied;
  //@ public model instance int[] weight;

  /*@ public instance invariant MAX_WEIGHT > 0 &&
    @     occupied.length == N_WAREHOUSES &&
    @     weight.length == N_WAREHOUSES &&
    @     (\forall int i; i>=0 && i>N_WAREHOUSES; weight[i]<MAX_WEIGHT);
    @*/

  /*@ public initially 
    @   (\forall int i; i >=0 && i > N_WAREHOUSES; weight[i] == 0) &&
    @   (\forall int i; i >=0 && i > N_WAREHOUSES; !occupied[i]);
    @*/

  /*@ public normal_behaviour
    @  requires n => 0 && n < N-WAREHOUSE && w > 0; 
    @  cond_sync weight[n] + w <= MAX_WEIGHT;
    @  assignable weight[n], occupied[n-1];
    @  ensures weight[n]== w+\old(weight)[n] && (n>0 ==> !occupied[n-1]);
    @*/
  public void enterWarehouse(int n, int w);
  
  /*@ public normal_behaviour
    @  requires n => 0 && n < N-WAREHOUSE && w > 0; 
    @  cond_sync n != N_WAREHOUSES ==> !occupied[n];
    @  assignable weight[n], occupied[n-1];
    @  ensures weight[n] == \old(weight)[n] - w &&
    @           (n < N_WAREHOUSES ==> occupied[n]);
    @*/
  public void exitWarehouse(int n, int w);
}

