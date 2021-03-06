package es.upm.babel.ccjml.samples.readerswriters.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWritersMonitorWritersPriority;

public class TestReadersWritersMonitorWritersPriority extends TestReadersWriters {

  // Run before every test
  @Before public void setUp() {
    this.readersPriority = false;
    resource = new ReadersWritersMonitorWritersPriority();
    trace = "";
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
