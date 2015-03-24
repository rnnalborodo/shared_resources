package es.upm.babel.ccjml.samples.semaphore.java.test;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import es.upm.babel.ccjml.samples.semaphore.java.Semaphore;
import es.upm.babel.cclib.Tryer;

public abstract class TestSemaphore {
    
  // The share resource
  protected Semaphore resource = null;
  
  protected int BOUND = 1;
  
  protected String trace = null;
  
  class P extends Tryer {
    // Constructor
    public P() {
    }
  
    // Just return a string representing the call
    private String call() {
      return "p();";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.p();
    }
  }

  class V extends Tryer {
    // Constructor
    public V() {
    }
  
    // Just return a string representing the call
    private String call() {
      return "v();";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.v();
    }
  }

  // Just a constant for waiting processes to set up
  final protected int DELAY_MIN_MS = 250;

  // No P can be performed after initialization
  @Test public void testPBlocksAfterInit() {
    P p = new P();
    p.start();
    p.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + p.call() + " should have blocked",
                       p.isBlocked());
  }

  // V unblocks properly
  @Test public void testVUnblocksProperly() {
    V v = new V();
    v.start();
    v.gimmeTime(DELAY_MIN_MS);
    
    V v1 = new V();
    v1.start();
    v1.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + v.call() + " shouldn't have blocked",
        !v.isBlocked());
    assertTrue(trace + "-> " + v1.call() + " should have blocked",
        v1.isBlocked());
    
    P p = new P();
    p.start();
    p.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + p.call() + " shouldn't have blocked",
        !p.isBlocked());
    assertTrue(trace + "-> " + v1.call() + " should have unblocked",
        !v1.isBlocked());
  }
  
  // P unblocks properly
  @Test public void testPUnblocksProperly() {
    P p = new P();
    p.start();
    p.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + p.call() + " should have blocked",
        p.isBlocked());
    
    V v = new V();
    v.start();
    v.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + v.call() + " shouldn't have blocked",
        !v.isBlocked());

    assertTrue(trace + "-> " + p.call() + " should have unblocked",
        !p.isBlocked());
  }
  
  // V blocks properly
  @Test public void testVblocksProperly() {
    V v[] = new V[BOUND+1];
    for (int i=0; i < BOUND+1; i++){
      v[i] = new V();
      v[i].start();
      v[i].gimmeTime(DELAY_MIN_MS);
    }

    for (int i=0; i < BOUND; i++){
      assertTrue(trace + "-> " + v[i].call() + " shouldn't have blocked",
          !v[i].isBlocked());
    }
    
    assertTrue(trace + "-> " + v[BOUND].call() + " should have blocked",
        v[BOUND].isBlocked());
  }

}
