package es.upm.babel.ccjml.samples.readerswriters.java;


public class ReadersWritersMonitorWritersPriority extends ReadersWritersMonitor{

  @Override
  //@ public normal_behaviour
  //@   assignable nothing;
  //@   ensures \result == writers == 0 && writersCond.waiting() == 0;
  protected boolean cpreBeforeRead() {
    return writers == 0 && writersCond.waiting() == 0;
  }
  
  @Override
  protected void unblockingCode00() {
    // prioritizing writers
    if (writersCond.waiting() > 0) {
      writersCond.signal();
    } else if (readersCond.waiting() > 0) { 
      // if no writer can be awaken
      readersCond.signal();
    }
  }
  
  @Override
  protected void unblockingCodeN0() {
    // prioritizing writers
    if (writersCond.waiting() > 0)
      return;
    else 
      if (readersCond.waiting() > 0)
        readersCond.signal();
  }

}
