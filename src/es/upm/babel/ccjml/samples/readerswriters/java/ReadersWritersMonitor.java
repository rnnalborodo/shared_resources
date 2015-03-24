package es.upm.babel.ccjml.samples.readerswriters.java;

import java.util.Random;

import es.upm.babel.cclib.Monitor;
import es.upm.babel.cclib.Monitor.Cond;

public class ReadersWritersMonitor extends AReadersWriters{

  protected Monitor mutex = new Monitor();
  protected Cond writersCond = mutex.newCond();
  protected Cond readersCond = mutex.newCond();

  // for ND
  private Random generator = new Random(System.currentTimeMillis());
  
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
    //@ assume true && repOK();
    mutex.enter();
    if (!cpreBeforeWrite()){
      writersCond.await();
    }
    
    //@ assert cpreBeforeWrite() && true && repOK();;
    writers++;
    mutex.leave();
  }

  public void afterWrite() { 
    //@ assume true && repOK;
    mutex.enter();
//    if (!true)
//      writersCond.await();
    
    //@ assert true && true && repOK();
    writers--;
    
    unblockingCode00();
    
    mutex.leave();
  }

  public void beforeRead() {
    //@ assume true;
    mutex.enter();
    if (!cpreBeforeRead()){
      readersCond.await();
    }
    
    //@ assert true && cpreBeforeRead() && repOk();
    readers++;

    unblockingCodeN0();

    mutex.leave();
  }

  public void afterRead()  { 
    mutex.enter();
    //@ assume true;
    
//    if (!true)
//        readersCond.await();
    
    //@ assert true && true && repOk();
    --readers;
    
    // checking for current state
    if (readers == 0)
      unblockingCode00();
    else 
      unblockingCodeN0();
    
    mutex.leave();
  }

  protected void unblockingCode00() {
    // 0 0 state - using random for ND
    // 0 readers, 0 writers
    // even for writer
    // odd for readers
    if (generator.nextInt() % 2 == 0 && writersCond.waiting() > 0){
      writersCond.signal();
    } else if (readersCond.waiting() > 0) {
      readersCond.signal();
    } else if (writersCond.waiting() > 0) { // if no reader can awake
      writersCond.signal();
    }
  }
  
  protected void unblockingCodeN0(){
    // n 0 state
    // n readers, 0 writers
    // Only readers can be awaken
    if (readersCond.waiting() > 0)
      readersCond.signal();
  }    
  
  @Override
  public String toString(){
    return super.toString()+ 
        " - [rW = "+ readersCond.waiting() + 
         " | Ww = "+ writersCond.waiting() +"]";
  }
  
}
