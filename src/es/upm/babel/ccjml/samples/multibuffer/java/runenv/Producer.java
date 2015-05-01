package es.upm.babel.ccjml.samples.multibuffer.java.runenv;

import java.util.Arrays;
import java.util.Calendar;

import es.upm.babel.ccjml.samples.multibuffer.java.Multibuffer;
import es.upm.babel.ccjml.samples.utils.DataFactory;
import es.upm.babel.cclib.ConcIO;

/**
 * Producer processes to generate items to be put in the buffer.
 */
public class Producer extends Thread {

  /** 
    * shared resource
    */
  private final Multibuffer sharedBuff;
  private final int maxProdNumber;

  public Producer(Multibuffer a, int m){
    this(a,m,-1);
  }
  
  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());
  
   /**.
    * @param a shared resource to put data into.
    * @param m item to be produced by the generato
    * @param max to add functionality for producing until 'max' items
    */
  public Producer(Multibuffer a, int m, int max) {
    sharedBuff = a;
    maxProdNumber = m;
  }

  /**
   * Produces generates numbers to be put inside the buffer.
   */
  @Override
  public void run() {
    while (true) {
      int n = random.nextInt(sharedBuff.maxData()/2) +1;
      Object[] els = new Object[n];
      for (int i = 0; i < els.length; i++) {
        els[i] =DataFactory.produce(maxProdNumber);
      }
      ConcIO.printfnl("Trying to PUT -->  "+ Arrays.deepToString(els));
      sharedBuff.put(els);
      ConcIO.printfnl("Put it! ("+Arrays.toString(els)+")");
    }
  }
}
