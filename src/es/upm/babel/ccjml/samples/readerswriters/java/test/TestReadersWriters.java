package es.upm.babel.ccjml.samples.readerswriters.java.test;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWriters;
import es.upm.babel.cclib.Tryer;

public abstract class TestReadersWriters {
    
  // The share resource
  protected ReadersWriters resource = null;
  
  protected String trace = null;
  
  protected Boolean readersPriority = null;
  
  class BeforeRead extends Tryer {  
    // Just return a string representing the call
    private String call() {
      return "beforeRead();";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.beforeRead();
    }
  }
  
  class AfterRead extends Tryer {  
    // Just return a string representing the call
    private String call() {
      return "afterRead();";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.afterRead();
    }
  }

  class BeforeWrite extends Tryer {  
    // Just return a string representing the call
    private String call() {
      return "beforeWrite();";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.beforeWrite();
    }
  }

  class AfterWrite extends Tryer {  
    // Just return a string representing the call
    private String call() {
      return "afterWrite();";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.afterWrite();
    }
  }
  
  // Just a constant for waiting processes to set up
  final protected int DELAY_MIN_MS = 250;

  @Test public void severalReadersAllowebAndWritewBlocksIfReading() {
    BeforeRead br[] = new BeforeRead[10];
    for (int i = 0; i < br.length; i++) {
      br[i] = new BeforeRead();
      br[i].start();
      br[i].gimmeTime(DELAY_MIN_MS);
    }
   
    BeforeWrite bw = new BeforeWrite();
    bw.start();
    bw.gimmeTime(DELAY_MIN_MS);
    
    for (int i = 0; i < br.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " shouldn't have blocked",
        !br[i].isBlocked());
    }
    assertTrue(trace + "-> " + bw.call() + " should have blocked",
       bw.isBlocked());
  }
  
  @Test public void onlyOneWriteAllowed() {
    BeforeWrite bw[] = new BeforeWrite[2];
    for (int i = 0; i < bw.length; i++) {
      bw[i] = new BeforeWrite();
      bw[i].start();
      bw[i].gimmeTime(DELAY_MIN_MS);
    }
   
    assertTrue(trace + "-> " + bw[0].call() + " shouldn't have blocked",
        !bw[0].isBlocked());
    assertTrue(trace + "-> " + bw[1].call() + " should have blocked",
       bw[1].isBlocked());
    
    AfterWrite aw = new AfterWrite();
    aw.start();
    aw.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + aw.call() + " shouldn't have blocked",
        !aw.isBlocked());
    assertTrue(trace + "-> " + bw[1].call() + " should have unblocked",
       !bw[1].isBlocked());
    
  }
  
  @Test public void beforeWriteDoesNotBlockAfterInit() {
    BeforeWrite bw = new BeforeWrite();
    bw.start();
    bw.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + bw.call() + " shouldn't have blocked",
       !bw.isBlocked());
  }
  
  @Test public void BeforeReadDoesNotBlockAfterInit() {
    BeforeRead bw = new BeforeRead();
    bw.start();
    bw.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + bw.call() + " shouldn't have blocked",
       !bw.isBlocked());
  }
  
  @Test public void severalWritersNotAllowed() {
    BeforeWrite bw[] = new BeforeWrite[2];
    for (int i = 0; i < bw.length; i++) {
      bw[i] = new BeforeWrite();
      bw[i].start();
      bw[i].gimmeTime(DELAY_MIN_MS);
    }
   
    assertTrue(trace + "-> " + bw[0].call() + " shouldn't have blocked",
      !bw[0].isBlocked());
    assertTrue(trace + "-> " + bw[1].call() + " should have blocked",
       bw[1].isBlocked());
  }
  
  @Test public void readersNotAllowedIfWriting() {
    BeforeWrite bw = new BeforeWrite();
    bw.start();
    bw.gimmeTime(DELAY_MIN_MS);
   
    BeforeRead br = new BeforeRead();
    br.start();
    br.gimmeTime(DELAY_MIN_MS);
   
    assertTrue(trace + "-> " + bw.call() + " shouldn't have blocked",
      !bw.isBlocked());
    assertTrue(trace + "-> " + br.call() + " should have blocked",
       br.isBlocked());
  }
  
  @Test public void readersAllowedAfterWriting() {
    BeforeWrite bw = new BeforeWrite();
    bw.start();
    bw.gimmeTime(DELAY_MIN_MS);
   
    BeforeRead br = new BeforeRead();
    br.start();
    br.gimmeTime(DELAY_MIN_MS);
   
    assertTrue(trace + "-> " + bw.call() + " shouldn't have blocked",
        !bw.isBlocked());
    assertTrue(trace + "-> " + br.call() + " should have blocked",
        br.isBlocked());
    
    AfterWrite aw = new AfterWrite ();
    aw.start();
    aw.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + aw.call() + " shouldn't have blocked",
        !aw.isBlocked());
    assertTrue(trace + "-> " + br.call() + " should have unblocked",
        !br.isBlocked());
  }
  
  @Test public void priorityTest() {
   
    BeforeRead br = new BeforeRead();
    br.start();
    br.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + br.call() + " shouldn't have blocked",
       !br.isBlocked());
    
    BeforeWrite bw = new BeforeWrite();
    bw.start();
    bw.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + bw.call() + " should have blocked",
        bw.isBlocked());

    br = new BeforeRead();
    br.start();
    br.gimmeTime(DELAY_MIN_MS);
    
    AfterRead ar = new AfterRead();
    ar.start();
    ar.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + ar.call() + " shouldn't have blocked",
        !ar.isBlocked());
    
    if (this.readersPriority != null) {
      if (readersPriority) {//readers priority           
        assertTrue(trace + "-> " + br.call() + " shouldn't have blocked",
            !br.isBlocked());
        
        assertTrue(trace + "-> " + bw.call() + " should have blocked",
            bw.isBlocked());

      } else{ // writers priority
        assertTrue(trace + "-> " + br.call() + " should have blocked",
            br.isBlocked());
        
        assertTrue(trace + "-> " + bw.call() + " shouldn't have blocked",
            !bw.isBlocked());
      }
    }
  }
  
  @Test public void simpleR() {
    BeforeRead br = new BeforeRead();
    br.start();
    br.gimmeTime(DELAY_MIN_MS);
   
    assertTrue(trace + "-> " + br.call() + " shouldn't have blocked",
      !br.isBlocked());
  }
  
  @Test public void simpleW() {
    BeforeWrite bw = new BeforeWrite();
    bw.start();
    bw.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + bw.call() + " shouldn't have blocked",
      !bw.isBlocked());
  }
}
