package es.upm.babel.ccjml.samples.multibuffer.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.multibuffer.java.MultibufferCSP;

public class TestMultibufferCSP extends TestMultibuffer {

  @Before public void setUp() {
    MultibufferCSP multiJCSP = new MultibufferCSP(MAX_DATA);
    ProcessManager pm = new ProcessManager(multiJCSP);
    this.multi = multiJCSP;
    this.trace = "";
    pm.start();
  }


  @After public void cleanUp() {
    multi = null;
    trace = null;
  }
}
