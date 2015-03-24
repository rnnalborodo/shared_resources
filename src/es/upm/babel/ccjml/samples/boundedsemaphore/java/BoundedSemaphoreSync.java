package es.upm.babel.ccjml.samples.boundedsemaphore.java;

import java.util.logging.Level;
import java.util.logging.Logger;

public class BoundedSemaphoreSync implements BoundedSemaphore{
  private int value = 0;
  private int upperBound  = 0;

  public BoundedSemaphoreSync(int upperBound){
    this.upperBound = upperBound;
  }

  @Override
  public synchronized void v(){
    while(this.value == upperBound) 
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(BoundedSemaphoreSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    this.value++;
    this.notify();
  }

  @Override
  public synchronized void p(){
    while(this.value == 0) 
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(BoundedSemaphoreSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    this.value--;
    this.notify();
  }
}