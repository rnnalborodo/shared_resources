package es.upm.babel.ccjml.samples.airport.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.airport.java.ControlTowerCSP;

public class TestControlTowerCSP extends TestControlTower {

  @Before public void setUp() {
    ControlTowerCSP towerJCSP = new ControlTowerCSP(MAX_DATA);
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
