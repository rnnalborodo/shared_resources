package es.upm.babel.ccjml.samples.readerswriters.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWritersCSPDeferredRequest;

public class TestReadersWritersCSPDeferredRequest extends TestReadersWriters {

  // Run before every test
  @Before public void setUp() {
    ReadersWritersCSPDeferredRequest rwCSPRes = new ReadersWritersCSPDeferredRequest();
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
