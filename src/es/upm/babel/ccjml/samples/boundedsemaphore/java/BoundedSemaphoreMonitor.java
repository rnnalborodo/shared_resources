package es.upm.babel.ccjml.samples.boundedsemaphore.java;

import es.upm.babel.cclib.Monitor;

/**
 * Semaphore implementation using monitors and conditions.
 * 
 * @author rnnalborodo
 */
public class BoundedSemaphoreMonitor implements BoundedSemaphore {

  private Monitor mutex;
  private Monitor.Cond v;
  private Monitor.Cond p;
  
  private final int bound;
  private int value;

  //@ensures \result == value < bound;
  private boolean cpreV(){
    return value < bound;
  }
  
  //@ensures \result == value > 0;
  private boolean cpreP(){
    return value > 0;
  }
  
  public BoundedSemaphoreMonitor(int _v){
    bound = _v;
    value = 0;
    mutex = new Monitor();
    p = mutex.newCond();
    v = mutex.newCond();
  }

  @Override
  public void v() {
    mutex.enter(); 
    //@ assume repOK() && true; //pre=true
    if (!cpreV()) 
      v.await();
    
    //@assume true && cpreV() && repOk();    
    value ++;
    
    if (p.waiting() >0) {
      p.signal();
    }
    
    // assert : only one thread is awakened
    mutex.leave();
  }

  @Override
  public void p(){
    mutex.enter();
    //@ assume repOK() && true; //pre=true
    if (!cpreP()) 
      p.await();
    
    //@assume true && cpreP() && repOk();
    value --;
    
    if (v.waiting() >0) {
      v.signal();
    }
    
    // assert : only one thread is awakened
    mutex.leave();
  }

  /*@
    @ public normal_behavior
    @   ensures bound >= value && value >= 0;
    @*/ 
  protected /*@ pure @*/ boolean repOk(){
    return bound >= value && value >= 0;
  }

  public /*@ pure @*/ String toString(){
    return "BS=[value = " +value+"]";
  }
  
}
