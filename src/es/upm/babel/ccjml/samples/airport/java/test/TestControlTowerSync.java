package es.upm.babel.ccjml.samples.airport.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.airport.java.ControlTowerSync;

public class TestControlTowerSync extends TestControlTower {

  @Before public void setUp() {
//    ControlTower towerJCSP = new ControlTower(MAX_DATA);
//    ProcessManager pm = new ProcessManager(towerJCSP);
    this.resource = new ControlTowerSync(MAX_DATA);
    this.trace = "";
  }


  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
