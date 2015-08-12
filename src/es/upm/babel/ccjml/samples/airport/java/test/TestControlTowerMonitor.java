package es.upm.babel.ccjml.samples.airport.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.airport.java.ControlTowerMonitor;

public class TestControlTowerMonitor extends TestControlTower {

  @Before public void setUp() {
//    ControlTower towerJCSP = new ControlTower(MAX_DATA);
//    ProcessManager pm = new ProcessManager(towerJCSP);
    this.resource = new ControlTowerMonitor(MAX_DATA);
    this.trace = "";
  }


  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
