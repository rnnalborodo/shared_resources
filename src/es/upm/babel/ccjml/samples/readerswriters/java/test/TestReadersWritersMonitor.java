package es.upm.babel.ccjml.samples.readerswriters.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWritersMonitor;

public class TestReadersWritersMonitor extends TestReadersWriters {

  // Run before every test
  @Before public void setUp() {
    resource = new ReadersWritersMonitor();
    trace = "";
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
