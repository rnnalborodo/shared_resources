package es.upm.babel.ccjml.samples.boundedsemaphore.java;

/** 
 * Bounded semaphore implementation using syncrhonized methods.
 * 
 * @author Babel Group 
 */

public class BoundedSemaphoreSync implements BoundedSemaphore{
  private int value = 0;
  private int upperBound  = 0;

  public BoundedSemaphoreSync(int upperBound){
    this.upperBound = upperBound;
  }

  @Override
  public synchronized void v(){
    //@ assume true;
    while(this.value == upperBound) 
      try {
        wait();
      } catch (InterruptedException ex) {}
    //@ assert value == 0;
    this.value++;
    
    this.notify();
  }

  @Override
  public synchronized void p(){
    //@ assume true;
    while(this.value == 0) 
      try {
        wait();
      } catch (InterruptedException ex) {}
    //@ assert value > 0;
    this.value--;
    this.notify();
  }
}