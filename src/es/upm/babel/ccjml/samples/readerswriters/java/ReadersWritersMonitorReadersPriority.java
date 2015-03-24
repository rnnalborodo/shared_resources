package es.upm.babel.ccjml.samples.readerswriters.java;


public class ReadersWritersMonitorReadersPriority extends ReadersWritersMonitor{

  @Override
  protected void unblockingCode00() {
    // priorizing readers
    if (readersCond.waiting() > 0) {
      readersCond.signal();
    } else if (writersCond.waiting() > 0) { 
      // if no reader can be awaken
      writersCond.signal();
    }
  }
  
  @Override
  protected void unblockingCodeN0() {
    // priorizing readers
    if (readersCond.waiting() > 0) {
      readersCond.signal();
    } 
  }

}
