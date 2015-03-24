package es.upm.babel.ccjml.samples.boundedsemaphore.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.boundedsemaphore.java.BoundedSemaphoreCSP;
import es.upm.babel.ccjml.samples.semaphore.java.test.TestSemaphore;

public class TestBoundedSemaphoreCSP extends TestBoundedSemaphore {

  @Before public void setUp() {
    BOUND = 1;
    BoundedSemaphoreCSP semCSP = new BoundedSemaphoreCSP(BOUND);
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
