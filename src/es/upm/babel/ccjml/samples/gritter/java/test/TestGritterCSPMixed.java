package es.upm.babel.ccjml.samples.gritter.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.gritter.java.GestorGritterCSPMixed;

public class TestGritterCSPMixed extends TestGritter {

  // Run before every test
  @Before public void setUp() {
    GestorGritterCSPMixed cspGG = new GestorGritterCSPMixed();
    ProcessManager pm = new ProcessManager(cspGG);
    this.resource = cspGG;
    this.trace = "";
    pm.start();
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
