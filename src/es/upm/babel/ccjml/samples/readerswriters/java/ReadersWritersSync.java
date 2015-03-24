package es.upm.babel.ccjml.samples.readerswriters.java;

public class ReadersWritersSync extends AReadersWriters{
  
  public synchronized void beforeWrite() {
    while (!cpreBeforeWrite()){
        try { 
            wait(); 
        } catch (InterruptedException ex) {}
    }
    //@ assert writeAllowed();
    writers++;
  }
  
  public synchronized void afterWrite() { 
    // assert writerPresent;
//    while (!true) { 
//      try {
//        wait();
//      } catch (InterruptedException ex) {
//        Logger.getLogger(ReadersWritersSync.class.getName()).log(Level.SEVERE, null, ex);
//      }
//    }
    writers--;
    notifyAll();
  }

  public synchronized void beforeRead() {
    while (!cpreBeforeRead()){
        try { 
            wait();
        } catch (InterruptedException ex) {}
    }
    //@ assert readAllowed();
    ++readers;
  }

  public synchronized void afterRead()  { 
    //@ assert activeReaders > 0; 
//    while (!true) { 
//      try {
//        wait();
//      } catch (InterruptedException ex) {
//        Logger.getLogger(ReadersWritersSync.class.getName()).log(Level.SEVERE, null, ex);
//      }
//    }
    --readers;
    notifyAll();
  }
  
}
