package es.upm.babel.ccjml.samples.observer.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.observer.java.EventManagerCSPDeferredRequest;

public class TestEventManagerCSPDeferredRequest extends TestEventManager {

  // Run before every test
  @Before public void setUp() {
    EventManagerCSPDeferredRequest rwCSPRes = new EventManagerCSPDeferredRequest(N_EVENTS, N_PROCESSES);
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
