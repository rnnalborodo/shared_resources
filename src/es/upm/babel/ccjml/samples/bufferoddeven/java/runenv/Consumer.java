package es.upm.babel.ccjml.samples.bufferoddeven.java.runenv;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEven;
import es.upm.babel.ccjml.samples.utils.DataProcessor;
import es.upm.babel.cclib.ConcIO;

/**
 * Consumer processes remove items from the buffer.
 */
public class Consumer extends Thread {

/**
 * Shared Buffer.
 */
private final BufferOddEven sharedBuff;

/**
 * Type of the consumer (inly gets even or odd numbers )
 */
private final BufferOddEven.Type type;

/**
 * @param a shared buffer where data are extracted from
   * @param type type of data to be extracted from the shared resource
 */
public Consumer(BufferOddEven a, BufferOddEven.Type type) {
  sharedBuff = a;
  this.type  = type;
}

 /**
  * Consumers extract items from the buffer based on its type
  */
@Override
 public void run() {
  int p;
  while (true) {
    ConcIO.printfnl("Trying to get " + (type.equals(BufferOddEven.Type.EVEN)?"EVEN":"ODD"));
     p = sharedBuff.get(type);
     ConcIO.printfnl("got it! ("+p+")");
     DataProcessor.process(p);
  }
 }
}
