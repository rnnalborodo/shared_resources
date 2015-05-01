package es.upm.babel.ccjml.samples.observer.java.test;

import static org.junit.Assert.assertTrue;

import java.util.Random;

import org.junit.Test;

import es.upm.babel.ccjml.samples.observer.java.EventManager;
import es.upm.babel.cclib.Tryer;

public abstract class TestEventManager {
  
  final int N_PROCESSES = 3;
  final int N_EVENTS = 1;
    
  final Random randomGenerator = new Random();
  
  // The share resource
  protected EventManager resource = null;
  
  protected String trace = null;
  
  class FireEvent extends Tryer {
    int eid;
    
    public FireEvent(int eit){
      eid = eit;
    }
    
    // Just return a string representing the call
    private String call() {
      return "fireEvent("+ eid +");";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.fireEvent(eid);
    }
  }  
  
  class Subscribe extends Tryer {
    int eid;
    int pid;
    
    public Subscribe(int pit, int eit){
      eid = eit;
      pid = pit;
    }
    
    // Just return a string representing the call
    private String call() {
      return "subscribe("+ pid +"," + eid +");";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.subscribe(pid, eid);
    }
  }

  class Unsubscribe extends Tryer {
    int eid;
    int pid;
    
    public Unsubscribe(int pit, int eit){
      eid = eit;
      pid = pit;
    }
    
    // Just return a string representing the call
    private String call() {
      return "unsubscribe("+ pid +"," + eid +");";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.unsubscribe(pid, eid);
    }
  }
  
  class Listen extends Tryer {
    int pid;
    
    public Listen(int pit){
      pid = pit;
    }
    
    // Just return a string representing the call
    private String call() {
      return "listen("+ pid +");";
    }
  
    // Call to the method
    public void toTry() {
      trace += call();
      resource.listen(pid);
    }
  }

  
  // Just a constant for waiting processes to set up
  final protected int DELAY_MIN_MS = 250;

  @Test public void subscriptionBeforeListening() {
    /* pid, eid */
    int pid = randomGenerator.nextInt(N_PROCESSES);
    int eid = randomGenerator.nextInt(N_EVENTS);
    Subscribe subscription = new Subscribe(pid, eid);
    subscription.start();
    subscription.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + subscription.call() + " shouldn't have blocked",
       !subscription.isBlocked());
    
    Listen listen = new Listen(pid);
    listen.start();
    listen.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + listen.call() + " should have blocked",
        listen.isBlocked());
    
    FireEvent fe = new FireEvent(eid);
    fe.start();
    fe.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + fe.call() + " shouldn't have blocked",
        !fe.isBlocked());

    assertTrue(trace + "-> " + listen.call() + " should have unblocked",
        !listen.isBlocked());

  }
  
  @Test public void unsubscritionBeforeListening() {
    /* pid, eid */
    int pid = randomGenerator.nextInt(N_PROCESSES);
    int eid = randomGenerator.nextInt(N_EVENTS);
    
    Subscribe subscription = new Subscribe(pid, eid);
    subscription.start();
    subscription.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + subscription.call() + " shouldn't have blocked",
       !subscription.isBlocked());

    Unsubscribe unsubscription = new Unsubscribe(pid, eid);
    unsubscription.start();
    unsubscription.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + unsubscription.call() + " shouldn't have blocked",
       !unsubscription.isBlocked());
    
    Listen listen = new Listen(pid);
    listen.start();
    listen.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + listen.call() + " should have blocked",
        listen.isBlocked());
    
    FireEvent fe = new FireEvent(eid);
    fe.start();
    fe.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + fe.call() + " shouldn't have blocked",
        !fe.isBlocked());

    assertTrue(trace + "-> " + listen.call() + " should have blocked",
        listen.isBlocked());


  }
  
  @Test public void onlyListening() {
    /* pid, eid */
    int pid = randomGenerator.nextInt(N_PROCESSES);
    
    Listen listen = new Listen(pid);
    listen.start();
    listen.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + listen.call() + " should have blocked",
        listen.isBlocked());
  }
  
  @Test public void doubleListening() {
    /* pid, eid */
    int pid = randomGenerator.nextInt(N_PROCESSES);
    int eid = randomGenerator.nextInt(N_EVENTS);
    
    Subscribe subscription = new Subscribe(pid, eid);
    subscription.start();
    subscription.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + subscription.call() + " shouldn't have blocked",
       !subscription.isBlocked());
    
    Listen listen = new Listen(pid);
    listen.start();
    listen.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + listen.call() + " should have blocked",
        listen.isBlocked());
    
    FireEvent fe = new FireEvent(eid);
    fe.start();
    fe.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + fe.call() + " shouldn't have blocked",
        !fe.isBlocked());

    assertTrue(trace + "-> " + listen.call() + " should have unblocked",
        !listen.isBlocked());

    listen = new Listen(pid);
    listen.start();
    listen.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + listen.call() + " should have blocked",
        listen.isBlocked());
  }
  
  @Test public void severalProcessOnSameEvent () {
    int eid = randomGenerator.nextInt(N_EVENTS);
    
    for (int i = 0; i < this.N_PROCESSES; i++) {
      Subscribe subscription = new Subscribe(i, eid);
      subscription.start();
      subscription.gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + subscription.call() + " shouldn't have blocked",
         !subscription.isBlocked());      
    }
    Listen[] listeners = new Listen[N_PROCESSES];
    
    for (int i = 0; i < this.N_PROCESSES; i++) {
      listeners[i] = new Listen(i);
      listeners[i].start();
      listeners[i].gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + listeners[i].call() + " should have blocked",
          listeners[i].isBlocked());
    }
    
    FireEvent fe = new FireEvent(eid);
    fe.start();
    fe.gimmeTime(DELAY_MIN_MS);
    
    assertTrue(trace + "-> " + fe.call() + " shouldn't have blocked",
        !fe.isBlocked());

    for (int i = 0; i < this.N_PROCESSES; i++) {
      assertTrue(trace + "-> " + listeners[i].call() + " should have unblocked",
          !listeners[i].isBlocked());
    }
  }
}
