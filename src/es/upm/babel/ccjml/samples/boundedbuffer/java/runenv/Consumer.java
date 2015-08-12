package es.upm.babel.ccjml.samples.boundedbuffer.java.runenv;

import es.upm.babel.ccjml.samples.boundedbuffer.java.BoundedBuffer;
import es.upm.babel.ccjml.samples.utils.DataProcessor;
import es.upm.babel.cclib.ConcIO;

/**
 * Consumer processes remove items from the buffer.
 */
public class Consumer extends Thread {

/**
 * Shared Buffer.
 */
private final BoundedBuffer sharedBuff;

/**
 * @param a shared buffer where data are extracted from
 */
public Consumer(BoundedBuffer a) {
  sharedBuff = a;
}

 /**
  * Consumers extract items from the buffer based on its type
  */
@Override
 public void run() {
  int p;
  while (true) {
    ConcIO.printfnl("Trying to get ");
     p = sharedBuff.get();
     ConcIO.printfnl("got it! ("+p+")");
     DataProcessor.process(p);
  }
 }
}
