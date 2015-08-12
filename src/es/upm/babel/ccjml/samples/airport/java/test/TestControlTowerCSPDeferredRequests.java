package es.upm.babel.ccjml.samples.airport.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.airport.java.ControlTowerCSPDeferredRequests;

public class TestControlTowerCSPDeferredRequests extends TestControlTower {

  @Before public void setUp() {
    ControlTowerCSPDeferredRequests towerJCSP = 
        new ControlTowerCSPDeferredRequests(MAX_DATA);
    ProcessManager pm = new ProcessManager(towerJCSP);
    this.resource = towerJCSP;
    this.trace = "";          
    pm.start();
  }


  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
