package es.upm.babel.ccjml.samples.readerswriters.java;

/** Implementation of ReadersWriters using synchronized methods. 
 *
 * @author Babel Group 
 */
public class ReadersWritersSync extends AReadersWriters{

  public synchronized void beforeWrite() {
    //@ assume true;
    while (!cpreBeforeWrite()){
      try { 
        wait(); 
      } catch (InterruptedException ex) {}
    }
    //@ assert writeAllowed();
    writers++;
  }

  public synchronized void afterWrite() { 
    //@ assume writer == 1;
//    while (!true) { 
//      try {
//        wait();
//      } catch (InterruptedException ex) { }
//    }
    writers--;
    notifyAll();
  }

  public synchronized void beforeRead() {
    //@ assume true
    while (!cpreBeforeRead()){
      try { 
        wait();
      } catch (InterruptedException ex) {}
    }
    //@ assert cpreBeforeRead();
    ++readers;
  }

  public synchronized void afterRead()  { 
    //@ assume readers > 0; 
//    while (!true) { 
//      try {
//        wait();
//      } catch (InterruptedException ex) {}
//    }
    //@ assert true;
    --readers;
    notifyAll();
  }

}
