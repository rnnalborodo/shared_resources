package es.upm.babel.ccjml.samples.warehouse.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.warehouse.java.WarehouseAccessControlCSP;

public class TestWarehouseAccessControlCSP extends TestWarehouseAccessControl {

  // Run before every test
  @Before public void setUp() {
    WarehouseAccessControlCSP rwCSPRes = 
                      new WarehouseAccessControlCSP(TestWarehouseAccessControl.N_WAREHOUSE, 
                                                    TestWarehouseAccessControl.MAX_WEIGHT);
    ProcessManager pm = new ProcessManager(rwCSPRes);
    this.resource = rwCSPRes;
    this.trace = "";
    pm.start();
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
