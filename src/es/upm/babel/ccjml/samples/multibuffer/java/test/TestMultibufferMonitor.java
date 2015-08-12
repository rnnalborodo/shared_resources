package es.upm.babel.ccjml.samples.multibuffer.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.multibuffer.java.MultibufferMonitor;

public class TestMultibufferMonitor extends TestMultibuffer {
  // Run before every test
  @Before public void setUp() {
    multi = new MultibufferMonitor(MAX_DATA);
    trace = "";
  }

  // Run after every test
  @After public void cleanUp() {
    multi = null;
    trace = null;
  }
}
