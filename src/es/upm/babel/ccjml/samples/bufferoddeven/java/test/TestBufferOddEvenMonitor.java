package es.upm.babel.ccjml.samples.bufferoddeven.java.test;

import org.junit.After;
import org.junit.Before;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEvenMonitor;

public class TestBufferOddEvenMonitor extends TestBufferOddEven {

  @Before public void setUp() {
//    MultibufferCSP multiJCSP = new MultibufferCSP(MAX_DATA);
//    ProcessManager pm = new ProcessManager(multiJCSP);
    this.boe = new BufferOddEvenMonitor(MAX_DATA);
    this.trace = "";
  }


  @After public void cleanUp() {
    boe = null;
    trace = null;
  }
}
