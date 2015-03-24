package es.upm.babel.ccjml.samples.utils;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * <em>Singleton</em> simulating the item process after removing it
 */
public class DataProcessor {
  /**
  * Average time
  */
 private static int avg_time_process_ms = 1000;

 /**
  * Number generator 
  */
 private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());

 private DataProcessor() {  }

 /**
  * Average proceesing time setter (in millis)
  * @param tmc_ms avg processing time 
  */
 public static void setAvgTime(int tmc_ms) {
    avg_time_process_ms = tmc_ms < 0 ? 0 : tmc_ms;
 }

 /**
  * Simulates the item processing period
  * @param item to be processed
  */
 public static void process(Object item) {
   int t;
//   ConcIO.printfnl("start processing : " + item + "...");
   t = random.nextInt(2 * avg_time_process_ms);
   try {
     Thread.sleep(t);
   } catch (InterruptedException ex) {
//     ConcIO.printfnl("exception caught: " + ex);
     Logger.getLogger(DataProcessor.class.getName()).log(Level.SEVERE, null, ex);
   } finally {
//     ConcIO.printfnl("end processing:  " + t + "ms.");
   }
 }
 
}
