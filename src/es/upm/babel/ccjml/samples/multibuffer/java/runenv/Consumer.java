package es.upm.babel.ccjml.samples.multibuffer.java.runenv;

import java.util.Arrays;
import java.util.Calendar;

import es.upm.babel.ccjml.samples.multibuffer.java.Multibuffer;
import es.upm.babel.ccjml.samples.utils.DataProcessor;
import es.upm.babel.cclib.ConcIO;

/**
 * Consumer processes remove items from the buffer.
 */
public class Consumer extends Thread {

/**
 * Shared Buffer.
 */
private final Multibuffer sharedBuff;

private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());

/**
 * @param a shared buffer where data are extracted from
 */
public Consumer(Multibuffer a) {
  sharedBuff = a;
}

 /**
  * Consumers extract items from the buffer based on its type
  */
@Override
 public void run() {
  while (true) {
    int n = random.nextInt(sharedBuff.maxData()/2) +1;
    ConcIO.printfnl("Trying to get ");
    Object[] p = sharedBuff.get(n);
    ConcIO.printfnl("got it! ("+Arrays.toString(p)+")");
    for (Object p1 : p) {
      DataProcessor.process(p1);
    }
  }
 }
}
