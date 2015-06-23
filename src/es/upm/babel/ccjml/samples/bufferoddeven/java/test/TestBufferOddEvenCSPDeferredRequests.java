package es.upm.babel.ccjml.samples.bufferoddeven.java.test;

import org.jcsp.lang.ProcessManager;
import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEven;
import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEvenCSP;
import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEvenCSPDeferredRequest;
import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEvenMonitor;

public class TestBufferOddEvenCSPDeferredRequests extends TestBufferOddEven {

  @Before public void setUp() {
    BufferOddEvenCSPDeferredRequest multiJCSP = new BufferOddEvenCSPDeferredRequest(MAX_DATA);
    ProcessManager pm = new ProcessManager(multiJCSP);
    this.boe = multiJCSP;
    this.trace = "";
    pm.start();
  }


  @After public void cleanUp() {
    boe = null;
    trace = null;
  }
}
