package es.upm.babel.ccjml.samples.semaphore.java;

import es.upm.babel.cclib.Monitor;

/**
 * Semaphore implementation using monitors and conditions.
 * 
 * @author rnnalborodo
 */
public class SemaphoreMonitor implements Semaphore {

  private Monitor mutex;
  private Monitor.Cond v;
  private Monitor.Cond p;
  
  private boolean value;
   //@ private represents sem <- value == 1;

  //@ensures \result == !value;
  private boolean cpreV(){
    return !value;
  }
  
  //@ensures \result == value;
  private boolean cpreP(){
    return value;
  }
  
  public SemaphoreMonitor(){
    value = false;
    mutex = new Monitor();
    v = mutex.newCond();
    p = mutex.newCond();
  }

  public void v() {
    mutex.enter();
    
    if (!cpreV()) 
      v.await();
    
    //@ assume cpreV();
    value = true;
    
    if (p.waiting() > 0)
      p.signal();

    mutex.leave();
  }

  @Override
  public void p(){
    mutex.enter();
    
    if (!cpreP()) 
      p.await();
    
    //@ assume cpreP();
    value = false;
    
    if (v.waiting() >0)
      v.signal();
    
    mutex.leave();
  }
  
  public String toString(){
    return "[ value= " + value + "]";
  }

}
