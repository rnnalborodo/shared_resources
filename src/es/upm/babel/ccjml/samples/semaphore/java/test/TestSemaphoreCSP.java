package es.upm.babel.ccjml.samples.semaphore.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.semaphore.java.SemaphoreCSP;

public class TestSemaphoreCSP extends TestSemaphore {

  @Before public void setUp() {
    SemaphoreCSP semCSP = new SemaphoreCSP();
    BOUND = 1;
    ProcessManager pm = new ProcessManager(semCSP);
    this.resource = semCSP;
    this.trace = "";
    pm.start();
  }


  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
