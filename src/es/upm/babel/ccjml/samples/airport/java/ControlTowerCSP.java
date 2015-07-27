package es.upm.babel.ccjml.samples.airport.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;

/** ControlTower implementation using CSP. 
 * 
 * @author Babel Group
 */ 
public class ControlTowerCSP implements ControlTower, CSProcess {

  //@ public invariant runways.length == monitors.length;
  private /*@ spec_public @*/boolean runways[];

  //@ ensures \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  private /*@ pure @*/ boolean cpreBeforeLanding(){
    return cpreBefore();
  }

  //@ ensures \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  private /*@ pure @*/ boolean cpreBeforeTakeOff(){
    return cpreBefore();
  }

  //@ ensures \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  private /*@ pure @*/ boolean cpreBefore(){
    for (int i = 0; i < runways.length; i++) {
      if (!runways[i]){
        return true;
      }
    }
    return false;
  }

  //@ requires r >=0 && r < runways.length;
  //@ ensures runways[r]; 
  private /*@ pure @*/ boolean preBeforeLanding(int r){
    return runways[r] && r >=0 && r < runways.length;
  }

  //@ requires r >=0 && r < runways.length;
  //@ ensures runways[r]; 
  private /*@ pure @*/ boolean preBeforeTakeOff(int r){
    return runways[r] && r >=0 && r < runways.length;
  }


  /** WRAPPER IMPLEMENTATION */
  /**
   *  Channel for receiving external request for each method
   */
  private final Any2OneChannel chBeforeLanding = Channel.any2one();
  private final Any2OneChannel chBeforeTakeOff = Channel.any2one();
  private final Any2OneChannel chAfterLanding  = Channel.any2one();
  private final Any2OneChannel chAfterTakeOff  = Channel.any2one();

  public ControlTowerCSP(int m) {
    runways = new boolean [m];
  }

  @Override
  public int beforeLanding() {
    //@ assume true;
    One2OneChannel ch = Channel.one2one();
    chBeforeLanding.out().write(ch);
    return (int)ch.in().read();
  }

  @Override
  public void afterLanding(int r) {
    //@assume runways[r] && r >=0 && r < runway.length;
    chAfterLanding.out().write(r);
  }

  @Override
  public int beforeTakeOff() {
    //@ assume true;
    One2OneChannel ch = Channel.one2one();
    chBeforeTakeOff.out().write(ch);
    return (int)ch.in().read();
  }

  @Override
  public void afterTakeOff(int r) {
    //@ assume runways[r] && r >=0 && r < runway.length;
    chAfterTakeOff.out().write(r);
  }

  /** SERVER IMPLEMENTATION */
  /**
   * Constants representing the method presented in the API
   */
  private static final int BEFORE_LANDING = 0;
  private static final int BEFORE_TAKEOFF = 1;
  private static final int AFTER_LANDING = 2;
  private static final int AFTER_TAKEOFF = 3;

  @Override
  public void run() {

    /** One entry for each method */
    Guard[] guards = {
        chBeforeLanding.in(),
        chBeforeTakeOff.in(),
        chAfterLanding.in(),
        chAfterTakeOff.in()
    };

    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean syncCond[] = new boolean[4];

    Alternative services = new Alternative(guards);
    int chosenService = 0;

    int runway;
    One2OneChannel innerCh;

    while (true) {
      syncCond[BEFORE_LANDING] = cpreBeforeLanding();
      syncCond[BEFORE_TAKEOFF] = cpreBeforeTakeOff() ;
      syncCond[AFTER_LANDING] = true;
      syncCond[AFTER_TAKEOFF] = true;
      //@ assert syncCond is consistent,i.e, all refreshments are done properly

      chosenService = services.fairSelect(syncCond);
      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0;
      //@ assume syncCond[chosenService];
      
      switch(chosenService){
        case BEFORE_LANDING:
          //@ assert cpreBeforeWrite();
          innerCh = (One2OneChannel) chBeforeLanding.in().read();
          innerCh.out().write(this.getRunway());
          break;
  
        case BEFORE_TAKEOFF:
          //@ assert cpreBeforeWrite();
          innerCh = (One2OneChannel) chBeforeTakeOff.in().read();
          innerCh.out().write(this.getRunway());
          break;
  
        case AFTER_LANDING: 
          //@ assert true;
          runway = (int) chAfterLanding.in().read();
          runways[runway] = false;
          break;
  
        case AFTER_TAKEOFF:
          //@ assert true;
          runway = (int) chAfterTakeOff.in().read();
          runways[runway] = false;
          break;
      }
    } // end while
  } // end run

  //@ requires cpreBeforeLanding && true && repOk();
  //@ ensures \result < runways.length && \result >= 0 && runways[\result];
  private int getRunway(){
    int ra = 0;
    for (int i = 0; i < runways.length; i++) {
      if (!runways[i]){
        ra = i;
        runways[ra] = true;
        break;
      }
    }
    return ra;
  }

}