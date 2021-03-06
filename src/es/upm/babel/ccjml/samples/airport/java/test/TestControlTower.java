package es.upm.babel.ccjml.samples.airport.java.test;

import static org.junit.Assert.assertTrue;

import java.sql.Timestamp;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.junit.Test;

import es.upm.babel.ccjml.samples.airport.java.ControlTower;
import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;
import es.upm.babel.cclib.Tryer;

public abstract class TestControlTower {

  // The share resource
  protected ControlTower resource = null;

  protected String trace = null;
  
  class BeforeLanding extends Tryer {  
    public int runaway;

    // Just return a string representing the call
    private String call() {
      return "beforeLanding() = "+ runaway +";";
    }
  
    // Call to the method
    public void toTry() {
      runaway = resource.beforeLanding();
      trace += call();
    }
  }
  
  class AfterLanding extends Tryer {  
    public int runway;

    public AfterLanding(int r) {
      runway = r;
    }
    
    // Just return a string representing the call
    private String call() {
      return "afterLanding("+runway+");";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      try {
        resource.afterLanding(runway);
      } catch (PreViolationSharedResourceException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
  }

  class BeforeTakeOff extends Tryer {  
    public int runaway;

    // Just return a string representing the call
    private String call() {
      return "beforeTakeOff() = "+ runaway +";";
    }
  
    // Call to the method
    public void toTry() {
      runaway = resource.beforeTakeOff();
      trace += call();
    }
  }

  class AfterTakeOff extends Tryer {  
    public int runway;

    public AfterTakeOff(int r) {
      runway = r;
    }
    
    // Just return a string representing the call
    private String call() {
      return "afterTakeOff("+runway+");";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      try {
        resource.afterTakeOff(runway);
      } catch (PreViolationSharedResourceException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
  }
  
  // Just a constant for waiting processes to set up
  final protected int DELAY_MIN_MS = 250;
  
  final protected static int MAX_DATA = 2;
 

  @Test public void severalLandingAtSameTime() {
    BeforeLanding br[] = new BeforeLanding[MAX_DATA+10];
    for (int i = 0; i < MAX_DATA+10; i++) {
      br[i] = new BeforeLanding();
      br[i].start();
      br[i].gimmeTime(DELAY_MIN_MS);
    }
   
//    BeforeWrite bw = new BeforeWrite();
//    bw.start();
//    bw.gimmeTime(DELAY_MIN_MS);
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " shouldn't have blocked",
        !br[i].isBlocked());
    }
    for (int i = MAX_DATA; i < br.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " should have blocked",
        br[i].isBlocked());
    }
  }
  
  @Test public void severalTakeOffAtSameTime() {
    BeforeTakeOff br[] = new BeforeTakeOff[MAX_DATA+10];
    for (int i = 0; i < MAX_DATA+10; i++) {
      br[i] = new BeforeTakeOff();
      br[i].start();
      br[i].gimmeTime(DELAY_MIN_MS);
    }
   
//    BeforeWrite bw = new BeforeWrite();
//    bw.start();
//    bw.gimmeTime(DELAY_MIN_MS);
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " shouldn't have blocked",
        !br[i].isBlocked());
    }
    for (int i = MAX_DATA; i < br.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " should have blocked",
        br[i].isBlocked());
    }
  }
  
  @Test public void takeOffsAllowsTakeOff() {
    BeforeTakeOff br[] = new BeforeTakeOff[MAX_DATA*2];
    for (int i = 0; i < MAX_DATA*2; i++) {
      br[i] = new BeforeTakeOff();
      br[i].start();
      br[i].gimmeTime(DELAY_MIN_MS);
    }
   
//    BeforeWrite bw = new BeforeWrite();
//    bw.start();
//    bw.gimmeTime(DELAY_MIN_MS);
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " shouldn't have blocked",
        !br[i].isBlocked());
    }
    for (int i = MAX_DATA; i < br.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " should have blocked",
        br[i].isBlocked());
    }
    
    AfterTakeOff ar[] = new AfterTakeOff[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      ar[i] = new AfterTakeOff(i);
      ar[i].start();
      ar[i].gimmeTime(DELAY_MIN_MS);
    }
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + ar[i].call() + " shouldn't have blocked",
        !ar[i].isBlocked());
    }

    for (int i = MAX_DATA; i < br.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(i + trace + "-> " + br[i].call() + " should have been unblocked",
        !br[i].isBlocked());
    } 
  }
  
  @Test public void takeOffsAllowsLanding() {
    BeforeTakeOff br[] = new BeforeTakeOff[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      br[i] = new BeforeTakeOff();
      br[i].start();
      br[i].gimmeTime(DELAY_MIN_MS);
    }
    
    BeforeLanding bl[] = new BeforeLanding[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      bl[i] = new BeforeLanding();
      bl[i].start();
      bl[i].gimmeTime(DELAY_MIN_MS);
    }
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " shouldn't have blocked",
        !br[i].isBlocked());
    }
    for (int i = MAX_DATA; i < bl.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + bl[i].call() + " should have blocked",
        bl[i].isBlocked());
    }
    
    AfterTakeOff ar[] = new AfterTakeOff[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      ar[i] = new AfterTakeOff(i);
      ar[i].start();
      ar[i].gimmeTime(DELAY_MIN_MS);
    }
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + ar[i].call() + " shouldn't have blocked",
        !ar[i].isBlocked());
    }

    for (int i = MAX_DATA; i < bl.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(i + trace + "-> " + bl[i].call() + " should have been unblocked",
        !bl[i].isBlocked());
    }
  }

  @Test public void landingsAllowsLandings() {
    BeforeLanding br[] = new BeforeLanding[MAX_DATA*2];
    for (int i = 0; i < MAX_DATA*2; i++) {
      br[i] = new BeforeLanding();
      br[i].start();
      br[i].gimmeTime(DELAY_MIN_MS);
    }
   
//    BeforeWrite bw = new BeforeWrite();
//    bw.start();
//    bw.gimmeTime(DELAY_MIN_MS);
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " shouldn't have blocked",
        !br[i].isBlocked());
    }
    for (int i = MAX_DATA; i < br.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " should have blocked",
        br[i].isBlocked());
    }
    
    AfterLanding ar[] = new AfterLanding[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      ar[i] = new AfterLanding(i);
      ar[i].start();
      ar[i].gimmeTime(DELAY_MIN_MS);
    }
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + ar[i].call() + " shouldn't have blocked",
        !ar[i].isBlocked());
    }

    for (int i = MAX_DATA; i < br.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(i + trace + "-> " + br[i].call() + " should have been unblocked",
        !br[i].isBlocked());
    } 
  }
  
  @Test public void LandingsAllowTakeOff() {
    
    BeforeLanding bl[] = new BeforeLanding[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      bl[i] = new BeforeLanding();
      bl[i].start();
      bl[i].gimmeTime(DELAY_MIN_MS);
    }
    
    BeforeTakeOff br[] = new BeforeTakeOff[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      br[i] = new BeforeTakeOff();
      br[i].start();
      br[i].gimmeTime(DELAY_MIN_MS);
    }

    for (int i = MAX_DATA; i < bl.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + bl[i].call() + " shouldn't have blocked",
        !bl[i].isBlocked());
    }
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + br[i].call() + " should have blocked",
        br[i].isBlocked());
    }
    
    AfterLanding ar[] = new AfterLanding[MAX_DATA];
    for (int i = 0; i < MAX_DATA; i++) {
      ar[i] = new AfterLanding(i);
      ar[i].start();
      ar[i].gimmeTime(DELAY_MIN_MS);
    }
    
    for (int i = 0; i < MAX_DATA; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(trace + "-> " + ar[i].call() + " shouldn't have blocked",
        !ar[i].isBlocked());
    }

    for (int i = MAX_DATA; i < br.length; i++) {
      //assertTrue(msg, condition that is asserted)
      assertTrue(i + trace + "-> " + br[i].call() + " should have been unblocked",
        !br[i].isBlocked());
    }
  }  
  
  
  protected static final int MAX_SR = MAX_DATA;
  static final int POOL_SIZE = MAX_SR * 4 ;
  private static final int NUMBER_OF_THREADS = POOL_SIZE * 200; //POOL_SIZE * 2;
  
  @Test public void aLoLocoWaitForIt() {
    
    ExecutorService executor = Executors.newFixedThreadPool(POOL_SIZE);
    for (int i = 0; i < NUMBER_OF_THREADS ; i++) {
      Runnable worker = () -> {
        Timestamp timestamp = new Timestamp(System.currentTimeMillis());

        try {
          System.out.println(timestamp + " | "+ Thread.currentThread().getName()+"] beforeTakeOff()");
          int rw = this.resource.beforeTakeOff();
          
          try {
            Thread.sleep(500);
          } catch (InterruptedException e) {
            e.printStackTrace();
          }

          System.out.println(timestamp + " | "+ Thread.currentThread().getName()+"] afterTakeOff("+ rw +")");
          this.resource.afterTakeOff(rw);
          System.out.println(timestamp + " | "+ Thread.currentThread().getName()+"] DONE!");
        } catch (Exception e) {
          e.printStackTrace();
        }
      };
      
      executor.execute(worker);
      
    }
    executor.shutdown();
    while (!executor.isTerminated()) {}
    System.out.println("Finished all threads");

  }
  
}