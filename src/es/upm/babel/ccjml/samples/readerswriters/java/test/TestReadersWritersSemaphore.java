package es.upm.babel.ccjml.samples.readerswriters.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWritersSemaphore;

public class TestReadersWritersSemaphore extends TestReadersWriters {

  // Run before every test
  @Before public void setUp() {
    resource = new ReadersWritersSemaphore();
    trace = "";
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
