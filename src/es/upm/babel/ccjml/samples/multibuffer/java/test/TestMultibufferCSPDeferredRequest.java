package es.upm.babel.ccjml.samples.multibuffer.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.multibuffer.java.MultibufferCSPDeferredRequest;

public class TestMultibufferCSPDeferredRequest extends TestMultibuffer {

  @Before public void setUp() {
    MultibufferCSPDeferredRequest multiJCSP = new MultibufferCSPDeferredRequest(MAX_DATA);
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
