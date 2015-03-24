package es.upm.babel.ccjml.samples.semaphore.java;

import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Semaphore implementation using syncrhonized methods.
 * 
 * @author rnnalborodo
 */
public class SemaphoreSync implements Semaphore {

  private boolean value;
   //@ private represents sem <- value == 1;

  public SemaphoreSync(){
    value = false;
  }

  @Override
  public synchronized void v() {
      while(value) 
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(SemaphoreSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    value = true;
    notifyAll();
  }

  @Override
  public synchronized void p(){
    while(!value) 
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(SemaphoreSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    value = false;
    notifyAll();
  }

}
