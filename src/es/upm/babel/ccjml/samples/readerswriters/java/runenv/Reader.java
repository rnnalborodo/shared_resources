package es.upm.babel.ccjml.samples.readerswriters.java.runenv;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWriters;
import es.upm.babel.ccjml.samples.utils.DataProcessor;
import es.upm.babel.cclib.ConcIO;

/**
 * Reader processes ask for permission to read and then read.
 */
public class Reader extends Thread {

  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());
  
  /**
   * Shared resource.
   */
  private final ReadersWriters sharedResource;

  /**
   * @param a shared resource to be read from
   */
  public Reader(ReadersWriters a) {
    sharedResource = a;
  }

  /**
   * Readers ask for permission to read and then read.
   */
  @Override
  public void run() {
    int p;
    while (true) {

    ConcIO.printfnl("Asking to read ");
    sharedResource.beforeRead();
    ConcIO.printfnl("Granted ");
    
    try {
      Thread.sleep(random.nextInt(1500));
    } catch (InterruptedException ex) {
    //     ConcIO.printfnl("exception caught: " + ex);
      Logger.getLogger(DataProcessor.class.getName()).log(Level.SEVERE, null, ex);
    } finally {
    //     ConcIO.printfnl("end processing:  " + t + "ms.");
    }

    ConcIO.printfnl("Trying to read ");
    sharedResource.afterRead();
    ConcIO.printfnl("read it! ");
    }
  }
}
