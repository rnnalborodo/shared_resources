package es.upm.babel.ccjml.samples.readerswriters.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWritersCSP;

public class TestReadersWritersCSP extends TestReadersWriters {

  // Run before every test
  @Before public void setUp() {
//    ReadersWritersCSPOptimized rwCSPRes = new ReadersWritersCSPOptimized();
    ReadersWritersCSP rwCSPRes = new ReadersWritersCSP();
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
