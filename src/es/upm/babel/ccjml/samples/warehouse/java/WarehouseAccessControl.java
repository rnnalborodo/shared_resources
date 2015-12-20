package es.upm.babel.ccjml.samples.warehouse.java;

/** 
 * A warehouse complex where autonomous robots move around fulfilling 
 * shipping orders. The weight of the robots, in any given warehouse, 
 * should never exceed a certain maximum weight.
 * 
 * @author BABEL Group - Technical University of Madrid
 */

interface WarehouseAccessControl {
  
  public void enterWarehouse(int n, int w);
  public void exitWarehouse(int n, int w);
}

