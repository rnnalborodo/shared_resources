package es.upm.babel.ccjml.samples.bufferoddeven.java.test;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEven;
import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEven.Type;
import es.upm.babel.ccjml.samples.multibuffer.java.Multibuffer;
import es.upm.babel.ccjml.samples.multibuffer.java.MultibufferSync;
import es.upm.babel.cclib.Tryer;

public abstract class TestBufferOddEven {

  // The share resource
  protected BufferOddEven boe = null;

  protected String trace = null;

  // Process that will try to put
  class Put extends Tryer {
    // Input data
    private int put_els = 0;

    // Output data
    // (no output)

    // Constructor
    public Put(int i) {
      this.put_els = i;
    }

    // Just return a string representing the call
    private String call() {
      return "put(" + put_els + ");";
    }

    // Call to the method
    public void toTry() {
      trace += call();
      boe.put(put_els);
    }
  }

  // Process that will try to get
  class Get extends Tryer {
    // Input data
    private BufferOddEven.Type get_n = BufferOddEven.Type.EVEN;

    // Output data
    private int get_result;

    // Constructor
    private Get() {
    }

    // Constructor
    public Get(BufferOddEven.Type n) {
      this.get_n = n;
    }

    private String call() {
      return "get(" + this.get_n + ");";
    }

    public void toTry() {
      trace += call();
      get_result = boe.get(get_n);
    }
  }

  // Just a constant for waiting processes to set up
  final protected int DELAY_MIN_MS = 25;

  // Constant for buffer capacity
  final protected int MAX_DATA = 4;

  // No sensible put gets blocked after initialization
  @Test public void test_put_do_not_block_after_init() {
    Put[] p = new Put[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      p[i] = new Put(i);
      p[i].start();
      p[i].gimmeTime(DELAY_MIN_MS);
    }
    int nData = 0;
    for (int i = 0; i < MAX_DATA; i++) {
      nData += i + 1;
      if (nData <= MAX_DATA) {
        assertTrue(trace + "-> " + p[i].call() + " shouldn't block",
            !p[i].isBlocked());
      }
    }
  }

  // No get should proceed after initialization
  @Test public void test_get_blocks_after_init() {
    Get[] g = new Get[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      g[i] = new Get((i % 2 == 1)?BufferOddEven.Type.EVEN:BufferOddEven.Type.ODD);
      g[i].start();
      g[i].gimmeTime(DELAY_MIN_MS);
    }
    for (int i = 0; i < MAX_DATA; i++) {
      assertTrue(trace + "-> " + g[i].call() + " should block",
          g[i].isBlocked());
    }
  }

  // Basic logic is observed
  @Test public void test_basic_logic() {
    // Repetitions just to force rotations in the pretending
    // circular implementation of the buffer
    for (int repeat = 0; repeat < 10; repeat++) {
      int nData = 0;
      int n;
      for (n = 1; nData + n <= MAX_DATA; n++) {
        Put p = new Put(n);
        p.start();
        p.gimmeTime(DELAY_MIN_MS);
        nData += n;

        Get g = new Get((n % 2 == 1)?BufferOddEven.Type.ODD:BufferOddEven.Type.EVEN);
        g.start();
        g.gimmeTime(DELAY_MIN_MS);
        assertTrue(trace + "-> " + g.call() + " shouldn't block -- " + boe.toString(),
            !g.isBlocked());
        assertTrue(trace + "-> " + g.call() + " should return " + n,
            g.get_result == n);
      }
    }
  }

  // Put blocks properly
  @Test public void test_put_blocks_properly() {
    for (int n = 0; n < MAX_DATA; n++) {
      Put g = new Put(n + 1);
      g.start();
      g.gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + g.call() + " shouldn't block",
          !g.isBlocked());
    }
    Put g = new Put(1);
    g.start();
    g.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + g.call() + " should block",
        g.isBlocked());

  }

  // Put unblocks properly
  @Test public void test_put_unblocks_properly() {
    for (int n = 0; n < MAX_DATA; n++) {
      Put g = new Put(n + 1);
      g.start();
      g.gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + g.call() + " shouldn't block",
          !g.isBlocked());
    }
    Put p = new Put(1);
    p.start();
    p.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + p.call() + " should block",
        p.isBlocked());

    Get g1 = new Get(Type.ODD);
    g1.start();
    g1.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + g1.call() + " shouldn't block",
        !g1.isBlocked());

    assertTrue(trace + "-> " + p.call() + " should unblock ",
        !p.isBlocked());

  }

  // GET blocks properly
  @Test public void test_get_odd_blocks_properly() {
    Put p = new Put(2);
    p.start();
    p.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + p.call() + " shouldn't block",
        !p.isBlocked());
    
    Get g = new Get(Type.ODD);
    g.start();
    g.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + g.call() + " should block",
        g.isBlocked());

  }

  // GET blocks properly
  @Test public void test_get_even_blocks_properly() {
    Put p = new Put(1);
    p.start();
    p.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + p.call() + " shouldn't block",
        !p.isBlocked());
    
    Get g = new Get(Type.EVEN);
    g.start();
    g.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + g.call() + " should block",
        g.isBlocked());

  }
  
  // GET blocks properly
  @Test public void test_get_unblocks_properly() {
    Put p = new Put(2);
    p.start();
    p.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + p.call() + " shouldn't block",
        !p.isBlocked());
    
    Get g = new Get(Type.ODD);
    g.start();
    g.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + g.call() + " should block",
        g.isBlocked());

    Get g1 = new Get(Type.EVEN);
    g1.start();
    g1.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + g1.call() + " shouldn't block",
        !g1.isBlocked());
    
    Put p1 = new Put(1);
    p1.start();
    p1.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + p1.call() + " shouldn't block",
        !p1.isBlocked());
    
    assertTrue(trace + "-> " + g.call() + " should unblock",
        !g.isBlocked());



  }


}
