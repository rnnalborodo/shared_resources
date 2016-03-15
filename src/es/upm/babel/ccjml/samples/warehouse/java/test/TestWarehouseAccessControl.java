package es.upm.babel.ccjml.samples.warehouse.java.test;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import es.upm.babel.ccjml.samples.warehouse.java.WarehouseAccessControl;
import es.upm.babel.cclib.Tryer;


public class TestWarehouseAccessControl {

  public static final int MAX_WEIGHT = 2;
  public static final int N_WAREHOUSE = 4;
	
  // The share resource
  protected WarehouseAccessControl resource = null;

  protected String trace = null;

  // Process that will try to put
  class EnterRobot extends Tryer {
    // Input data
    private int weight = 0;
    private int warehouse = 0;
    private int robotId;
    
    // Output data
    // (no output)

    // Constructor
    public EnterRobot(int a, int _n, int _w) {
      this.robotId = a;
      this.weight = _w;
      this.warehouse = _n;
    }

    // Just return a string representing the call
    private String call() {
      return robotId+":enterWarehouse(" + warehouse +","+ weight + ");";
    }

    // Call to the method
    public void toTry() {
      trace += call();
      resource.enterWarehouse(warehouse, weight);
    }
  }
    
  // Process that will try to put
  class ExitRobot extends Tryer {
    // Input data
    private int weight = 0;
    private int warehouse = 0;
    private int robotId;

    // Output data
    // (no output)

    // Constructor
    public ExitRobot(int a, int _n, int _w) {
      this.robotId = a;
      this.weight = _w;
      this.warehouse = _n;
    }

    // Just return a string representing the call
    private String call() {
      return robotId+":exitWarehouse(" + warehouse +","+ weight + ");";
    }

    // Call to the method
    public void toTry() {
      trace += call();
      resource.exitWarehouse(warehouse, weight);
    }
  }

  // Just a constant for waiting processes to set up
  final protected int DELAY_MIN_MS = 25;

  // No sensible blockes after initialization
  @Test 
  public void enteringWarehouse0() {
    EnterRobot[] p = new EnterRobot[MAX_WEIGHT];
    for (int i = 0; i < MAX_WEIGHT; i++) {
      p[i] = new EnterRobot(i,0,1);
      p[i].start();
      p[i].gimmeTime(DELAY_MIN_MS);
    }
    EnterRobot p1 = new EnterRobot(-1,0,1);
    p1.start();
    p1.gimmeTime(DELAY_MIN_MS);

    for (int i = 0; i < MAX_WEIGHT; i++) {
      assertTrue(trace + "-> " + p[i].call() + " shouldn't block",
                       !p[i].isBlocked());
    }
    assertTrue(trace + "-> " + p1.call() + " should block",
                       p1.isBlocked());
  }  
  
  // a robot can go through the whole warehouse without being bloked
  @Test 
  public void goingThrough() {
    EnterRobot[] er = new EnterRobot[N_WAREHOUSE];
    ExitRobot[] xr = new ExitRobot[N_WAREHOUSE];
    for (int i = 0; i < N_WAREHOUSE; i++) {
      er[i] = new EnterRobot(i,0,MAX_WEIGHT);
      er[i].start();
      er[i].gimmeTime(DELAY_MIN_MS);
      xr[i] = new ExitRobot(i,0,MAX_WEIGHT);
      xr[i].start();
      xr[i].gimmeTime(DELAY_MIN_MS);

    }
    
    for (int i = 0; i < N_WAREHOUSE; i++) {
      assertTrue(trace + "-> " + er[i].call() + " shouldn't block",
          !er[i].isBlocked());
      assertTrue(trace + "-> " + xr[i].call() + " shouldn't block",
          !xr[i].isBlocked());
    }
  }


}
