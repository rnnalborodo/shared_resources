package es.upm.babel.ccjml.samples.utils;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * <em>singleton</em> emulating items production.
 * For simplicity's sake, <em>Object</em> are created 
 */
public class DataFactory {

  /**
  * Average production time
  */
  private static int avg_production_time = 1000;

  /**
  * Random number generator.
  */
  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());
  private static  int maxItem;

  private DataFactory() { }

  /**
   * Set average production time expressed in ms  .
   * @param tmp_ms
   */
  public static void setAverageProductionTime(int tmp_ms) {
    avg_production_time = tmp_ms < 0 ? 0 :tmp_ms;
  }

  /**
  * Emulates the creation of an item
   * @param m max number to be produced
   * @return item to be inserted
  */
  public static int produce(int m) {
    maxItem = m;
    int item;
    int t;
    //     ConcIO.printfnl("start production...");
    t = random.nextInt(2 * avg_production_time);
    try {
      Thread.sleep(t);
    } catch (InterruptedException ex) {
    //         ConcIO.printfnl("exception caught: " + ex);
      Logger.getLogger(DataFactory.class.getName()).log(Level.SEVERE, null, ex);
    } finally {
      item = random.nextInt(maxItem);
    //         ConcIO.printfnl("end production: " + item + " in " + t + "ms.");
    }
    return item;
  }
}
