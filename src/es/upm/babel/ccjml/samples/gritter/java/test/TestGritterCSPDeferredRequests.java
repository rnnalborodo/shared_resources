package es.upm.babel.ccjml.samples.gritter.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.gritter.java.GestorGritterCSPDeferredRequests;

public class TestGritterCSPDeferredRequests extends TestGritter {

  // Run before every test
  @Before public void setUp() {
    GestorGritterCSPDeferredRequests cspGG = new GestorGritterCSPDeferredRequests();
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
