package es.upm.babel.ccjml.samples.boundedsemaphore.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.boundedsemaphore.java.BoundedSemaphoreMonitor;
import es.upm.babel.ccjml.samples.semaphore.java.test.TestSemaphore;

public class TestBoundedSemaphoreMonitor extends TestBoundedSemaphore {

  // Run before every test
  @Before public void setUp() {
    resource = new BoundedSemaphoreMonitor(BOUND);
    trace = "";
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
