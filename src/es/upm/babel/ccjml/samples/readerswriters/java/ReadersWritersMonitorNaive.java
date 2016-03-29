package es.upm.babel.ccjml.samples.readerswriters.java;

import es.upm.babel.cclib.Monitor;
import es.upm.babel.cclib.Monitor.Cond;

public class ReadersWritersMonitorNaive{

  protected int readers = 0;
  protected int writers = 0;
  
  protected Monitor mutex = new Monitor();
  protected Cond writersCond = mutex.newCond();
  protected Cond readersCond = mutex.newCond();
  
  //@ public normal_behaviour
  //@   ensures \result == (writers == 0 && readers == 0);  
  protected /*@pure@*/ boolean cpreBeforeWrite() {
    return readers == 0 && writers == 0 ;
  }

  //@ public normal_behaviour
  //@   assignable nothing;
  //@   ensures \result == (writers == 0);
  protected boolean cpreBeforeRead() {
    return writers ==0;
  }

  
  public void beforeWrite() {
    mutex.enter();
    if (!cpreBeforeWrite())
      writersCond.await();
    
    writers++;
    
    dummyUnblockingCode();
    mutex.leave();
  }

  public void afterWrite() { 
    mutex.enter();
    if (!true) writersCond.await();
    
    writers--;
    
    dummyUnblockingCode();
    mutex.leave();
  }

  public void beforeRead() {
    mutex.enter();
    if (!cpreBeforeRead())
      readersCond.await();
    
    readers++;

    dummyUnblockingCode();
    mutex.leave();
  }

  public void afterRead()  { 
    mutex.enter();
    if (!true)  readersCond.await();
    
    --readers;
    
    // checking for current state
    dummyUnblockingCode();
    mutex.leave();
  }

  protected void dummyUnblockingCode() {
    if (readersCond.waiting() > 0 && writers == 0)
      readersCond.signal();
    else if (writersCond.waiting() > 0 && 
               writers == 0 && readers == 0)
      writersCond.signal();
  }
}
