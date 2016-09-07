package es.upm.babel.ccjml.samples.gritter.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.gritter.java.GestorGritterMonitorIndexClientes;

public class TestGritterMonitorIndexClientes extends TestGritter {

  // Run before every test
  @Before public void setUp() {
    resource = new GestorGritterMonitorIndexClientes();
    trace = "";
  }

  // Run after every test
  @After public void cleanUp() {
    resource = null;
    trace = null;
  }
}
