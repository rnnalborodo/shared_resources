package es.upm.babel.ccjml.samples.observer.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.observer.java.EventManagerSync;

public class TestEventManagerSync extends TestEventManager {

  // Run before every test
  @Before public void setUp() {

    resource = new EventManagerSync(N_EVENTS, N_PROCESSES);
    trace = "";
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
