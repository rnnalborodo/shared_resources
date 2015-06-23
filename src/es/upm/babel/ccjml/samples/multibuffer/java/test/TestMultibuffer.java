package es.upm.babel.ccjml.samples.multibuffer.java.test;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import es.upm.babel.ccjml.samples.multibuffer.java.Multibuffer;
import es.upm.babel.ccjml.samples.multibuffer.java.MultibufferSync;
import es.upm.babel.cclib.Tryer;

public abstract class TestMultibuffer {
    
    // The share resource
    protected Multibuffer multi = null;

    protected String trace = null;

    // Process that will try to put
    class Put extends Tryer {
        // Input data
        private Object[] put_els = null;

        // Output data
        // (no output)

        // Constructor
        private Put() {
        }

        // Constructor
        public Put(Object[] els) {
            this.put_els = els;
        }

        // Just return a string representing the call
        private String call() {
            String args = " ";
            for (int i = 0; i < this.put_els.length; i++) {
                args += this.put_els[i].toString() + " ";
            }
            return "put(" + args + ");";
        }

        // Call to the method
        public void toTry() {
            trace += call();
            multi.put(put_els);
        }
    }

    // Process that will try to get
    class Get extends Tryer {
        // Input data
        private int get_n = 0;

        // Output data
        private Object[] get_result;

        // Constructor
        private Get() {
        }

        // Constructor
        public Get(int n) {
            this.get_n = n;
        }

        private String call() {
            return "get(" + this.get_n + ");";
        }

        public void toTry() {
            trace += call();
            get_result = multi.get(get_n);
        }
    }

    // Just a constant for waiting processes to set up
    final protected int DELAY_MIN_MS = 25;

    // Constant for buffer capacity
    final protected int MAX_DATA = 4;
    final private int MAX_DATA_ = MAX_DATA /2 ;

    // Internal counter to generate consecutive integers
    private int id = 0;

    // Returns a new array of integers
    private Integer[] createInts(int n) {
        Integer[] result = new Integer[n];
        for (int i = 0; i < result.length; i++) {
            result[i] = new Integer(id);
            id++;
        }
        return result;
    }

    // No sensible put gets blocked after initialization
    @Test public void test_put_do_not_block_after_init() {
        Put[] p = new Put[MAX_DATA_];
        for (int i = 0; i < MAX_DATA_; i++) {
            p[i] = new Put(createInts(i+1));
            p[i].start();
            p[i].gimmeTime(DELAY_MIN_MS);
        }
        int nData = 0;
        for (int i = 0; i < MAX_DATA_; i++) {
            nData += i + 1;
            if (nData <= MAX_DATA) {
                assertTrue(trace + "-> " + p[i].call() + " shouldn't block",
                           !p[i].isBlocked());
            }
            else {
                assertTrue(trace + "-> " + p[i].call() + " should block",
                           p[i].isBlocked());
            }
        }
    }

    // No get should proceed after initialization
    @Test public void test_get_blocks_after_init() {
        Get[] g = new Get[MAX_DATA_];
        for (int i = 0; i < MAX_DATA_; i++) {
            g[i] = new Get(i+1);
            g[i].start();
            g[i].gimmeTime(DELAY_MIN_MS);
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            assertTrue(trace + "-> " + g[i].call() + " should block",
                       g[i].isBlocked());
        }
    }

    // Basic logic is observed
    @Test public void test_basic_logic() {
        int id = 0;
        // Repetitions just to force rotations in the pretending
        // circular implementation of the buffer
        for (int repeat = 0; repeat < 10; repeat++) {
            int nData = 0;
            int nGets;
            int n;
            for (n = 1; nData + n <= MAX_DATA_; n++) {
                Put p = new Put(createInts(n));
                p.start();
                p.gimmeTime(DELAY_MIN_MS);
                nData += n;
            }
            nGets = n - 1;
            for (n = nGets; n > 0; n--) {
                Get g = new Get(n);
                g = new Get(n);
                g.start();
                g.gimmeTime(DELAY_MIN_MS);
                assertTrue(trace + "-> " + g.call() + " shouldn't block",
                           !g.isBlocked());
                assertTrue(trace + "-> " + g.call() + " should return " + n + "objects",
                           g.get_result.length == n);
                for (int i = 0; i < n; i++) {
                    assertTrue(trace + "-> " + g.call() + " should return " + id + " as " + i + "-th element",
                               g.get_result[i].equals(id));
                    id++;
                }
            }
        }
    }

    private void put1By1(int n) {
        // Assume there is at least n holes
        for (int i = 0; i < n; i++) {
            Put p = new Put(createInts(1));
            p.start();
            p.gimmeTime(DELAY_MIN_MS);
            assertTrue(trace + "-> " + p.call() + " shouldn't block",
                       !p.isBlocked());
        }
    }

    private void get1By1(int n) {
        // Assume there is at least n elements
        for (int i = 0; i < n; i++) {
            Get g = new Get(1);
            g.start();
            g.gimmeTime(DELAY_MIN_MS);
            assertTrue(trace + "-> " + g.call() + " shouldn't block",
                       !g.isBlocked());
        }
    }

    // Put blocks properly
    @Test public void test_put_blocks_properly() {
        for (int n = 1; n < MAX_DATA_; n++) {
            multi = new MultibufferSync(MAX_DATA_);
            trace = "";
            put1By1(n);
            Put p = new Put(createInts(MAX_DATA_ - n + 1));
            p.start();
            p.gimmeTime(DELAY_MIN_MS);
            assertTrue(trace + "-> " + p.call() + " should block",
                       p.isBlocked());
        }
    }

    // Put blocks properly
    @Test public void test_get_blocks_properly() {
        for (int n = 1; n < MAX_DATA_; n++) {
            multi = new MultibufferSync(MAX_DATA_);
            trace = "";
            put1By1(n);
            Get g = new Get(n + 1);
            g.start();
            g.gimmeTime(DELAY_MIN_MS);
            assertTrue(trace + "-> " + g.call() + " should block",
                       g.isBlocked());
        }
    }

    // Put unblocks properly
    @Test public void test_put_unblocks_properly() {
        Put[] p = new Put[MAX_DATA_];
        put1By1(MAX_DATA);
        for (int i = 0; i < MAX_DATA_; i++) {
            p[i] = new Put(createInts(i+1));
            p[i].start();
            p[i].gimmeTime(DELAY_MIN_MS);
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            assertTrue(trace + "-> " + p[i].call() + " should block",
                       p[i].isBlocked());
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            Get g = new Get(i + 1);
            g.start();
            g.gimmeTime(DELAY_MIN_MS);
            assertTrue(trace + "-> " + g.call() + " shouldn't block",
                       !g.isBlocked());
            assertTrue(trace + "-> " + p[i].call() + " should have unblocked",
                       !p[i].isBlocked());
        }
    }

    // Get unblocks properly
    @Test public void test_get_unblocks_properly() {
        Get[] g= new Get[MAX_DATA_];
        for (int i = 0; i < MAX_DATA_; i++) {
            g[i] = new Get(i+1);
            g[i].start();
            g[i].gimmeTime(DELAY_MIN_MS);
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            assertTrue(trace + "-> " + g[i].call() + " should block",
                       g[i].isBlocked());
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            Put p = new Put(createInts(i + 1));
            p.start();
            p.gimmeTime(DELAY_MIN_MS);
            assertTrue(trace + "-> " + p.call() + " shouldn't block",
                       !p.isBlocked());
            assertTrue(trace + "-> " + g[i].call() + " should have unblocked",
                       !g[i].isBlocked());
        }
    }

    // Put priority: FIFO
    @Test public void test_put_fifo_priority() {
        Put[] p = new Put[MAX_DATA_];
        put1By1(MAX_DATA_);
        for (int i = 0; i < MAX_DATA_; i++) {
            p[i] = new Put(createInts(i+1));
            p[i].start();
            p[i].gimmeTime(DELAY_MIN_MS);
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            assertTrue(trace + "-> " + p[i].call() + " should block",
                       p[i].isBlocked());
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            Get g = new Get(MAX_DATA_ - i);
            g.start();
            g.gimmeTime(DELAY_MIN_MS);
            assertTrue(trace + "-> " + g.call() + " shouldn't block",
                       !g.isBlocked());
            for (int j = i + 1; j < MAX_DATA_; j++) {
                assertTrue(trace + "-> " + p[j].call() + " shouldn't have unblocked",
                           !p[j].isBlocked());
            }
            assertTrue(trace + "-> " + p[i].call() + " should have unblocked",
                       !p[i].isBlocked());
        }
    }

    // Get priority: FIFO
    @Test public void test_get_fifo_priority() {
        Get[] g = new Get[MAX_DATA_];
        for (int i = 0; i < MAX_DATA_; i++) {
            g[i] = new Get(i+1);
            g[i].start();
            g[i].gimmeTime(DELAY_MIN_MS);
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            assertTrue(trace + "-> " + g[i].call() + " should block",
                       g[i].isBlocked());
        }
        for (int i = 0; i < MAX_DATA_; i++) {
            Put p = new Put(createInts(MAX_DATA_ - i));
            p.start();
            p.gimmeTime(DELAY_MIN_MS);
            assertTrue(trace + "-> " + p.call() + " shouldn't block",
                       !p.isBlocked());
            for (int j = i + 1; j < MAX_DATA_; j++) {
                assertTrue(trace + "-> " + g[j].call() + " shouldn't have unblocked",
                           !g[j].isBlocked());
            }
            assertTrue(trace + "-> " + g[i].call() + " should have unblocked",
                       !g[i].isBlocked());
        }
    }
}
