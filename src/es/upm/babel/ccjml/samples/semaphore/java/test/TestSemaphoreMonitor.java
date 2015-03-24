package es.upm.babel.ccjml.samples.semaphore.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.semaphore.java.SemaphoreMonitor;

public class TestSemaphoreMonitor extends TestSemaphore {
  // Run before every test
  
  @Before public void setUp() {
    resource = new SemaphoreMonitor();
    BOUND = 1;
    trace = "";
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
