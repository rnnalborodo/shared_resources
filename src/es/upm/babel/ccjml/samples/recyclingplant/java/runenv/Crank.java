package es.upm.babel.ccjml.samples.recyclingplant.java.runenv;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

/** 
 * Class representing a Crank that pick up steel and drop it into the container
 * @author rnnalborodo
 */

public class Crank {
  
  // Max amount of available cranks
  public static final int MAX_CRANKS = 1;

  // Min load weight for a cranks
  public static final int MIN_W_CRANK = 1000;

  // Max load weight for a cranks
  static final int MAX_W_CRANK = 2000;

  // Minimal time for droping the load
  private static final int MIN_TIME_DROP_MS = MIN_W_CRANK / 10;

  // Maximal time for droping the load
  private static final int MAX_TIME_DROP_MS = MAX_W_CRANK / 10;

  private static final java.util.concurrent.locks.Lock lock = new java.util.concurrent.locks.ReentrantLock();

  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());

  // Crank loads
  private static final int[] loads = new int[MAX_CRANKS];

  // Objectless class
  private Crank() {
    for (int idCrank = 0; idCrank < MAX_CRANKS; idCrank++) {
      loads[idCrank] = 0;
    }
  }

  // Pick up the steel and return the load weight
  // 1 <= idCrank <= MAX_CRANKS
  // MIN_W_CRANK <= result <= MAX_W_CRANK
  public static int pick(int idGrua) {
    int load;
    lock.lock();
    try {
      load = MIN_W_CRANK + random.nextInt(MAX_W_CRANK - MIN_W_CRANK);
      loads[idGrua] = load;
    } finally {
      lock.unlock();
    }
    
    try {
      Thread.sleep(2 * load);
    } catch (InterruptedException x) {}
    return load;
  }

    // Mueve la grua hasta el punto de descarga y
    // desactiva el electroiman
  public static void drop(int idGrua) {
    int t = 0;
    lock.lock();
    try {
      t = random.nextInt(MAX_TIME_DROP_MS - MIN_TIME_DROP_MS);
      Container.increment(loads[idGrua]);
      loads[idGrua] = 0;
    } catch (Exception x) {
    } finally {
      lock.unlock();
    }
    try {
      Thread.sleep(MIN_TIME_DROP_MS + t);
    } catch (InterruptedException ex) {
      Logger.getLogger(Crank.class.getName()).log(Level.SEVERE, null, ex);
    }
  }
}
