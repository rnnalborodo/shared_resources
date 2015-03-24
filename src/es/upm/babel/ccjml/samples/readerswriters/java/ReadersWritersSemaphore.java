package es.upm.babel.ccjml.samples.readerswriters.java;

import java.util.concurrent.Semaphore;
import java.util.logging.Level;
import java.util.logging.Logger;

public class ReadersWritersSemaphore implements ReadersWriters {
  
  protected Semaphore mutexRead = new Semaphore(1);
  protected Semaphore mutexAccess = new Semaphore(1);
  protected int readersCounter=0;
  
  
  public void beforeRead(){
    try {
      mutexRead.acquire();
      if (++readersCounter == 1) {
        mutexAccess.acquire();
      }
      mutexRead.release();
    } catch (InterruptedException ex) {
      Logger.getLogger(ReadersWritersSemaphore.class.getName()).log(Level.SEVERE, null, ex);
    }
  }

  public void afterRead() {
    try {
      mutexRead.acquire();
      if (--readersCounter == 0) {
        mutexAccess.release();
      }
      mutexRead.release();
    } catch (InterruptedException ex) {
      Logger.getLogger(ReadersWritersSemaphore.class.getName()).log(Level.SEVERE, null, ex);
    }
  }

  public void beforeWrite(){
    try {
      mutexAccess.acquire();
    } catch (InterruptedException ex) {
      Logger.getLogger(ReadersWritersSemaphore.class.getName()).log(Level.SEVERE, null, ex);
    }
  }

  public void afterWrite(){
    mutexAccess.release();
  }
}