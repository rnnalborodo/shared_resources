package es.upm.babel.ccjml.samples.gritter.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.gritter.java.GestorGritterCSP;

public class TestGritterCSP extends TestGritter {

  // Run before every test
  @Before public void setUp() {
    GestorGritterCSP rwCSPRes = new GestorGritterCSP();
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
