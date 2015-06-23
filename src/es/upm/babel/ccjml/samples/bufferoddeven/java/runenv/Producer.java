package es.upm.babel.ccjml.samples.bufferoddeven.java.runenv;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEven;
import es.upm.babel.ccjml.samples.utils.DataFactory;
import es.upm.babel.cclib.ConcIO;

/**
 * Producer processes to generate items to be put in the buffer.
 */
public class Producer extends Thread {

  /** 
    * shared resource
    */
  private final BufferOddEven sharedBuff;
  private final int maxProdNumber;

  public Producer(BufferOddEven a, int m){
    this(a,m,-1);
  }
   /**.
    * @param a shared resource to put data into.
    * @param m item to be produced by the generato
    * @param max to add functionality for producing until 'max' items
    */
  public Producer(BufferOddEven a, int m, int max) {
    sharedBuff = a;
    maxProdNumber = m;
  }

  /**
   * Produces generates numbers to be put inside the buffer.
   */
  @Override
  public void run() {
    int p;
    while (true) {
      p = DataFactory.produce(maxProdNumber);
      ConcIO.printfnl("Trying to PUT -->  "+ p);
      sharedBuff.put(p);
      ConcIO.printfnl("Put it! ("+p+")");
    }
  }
}
