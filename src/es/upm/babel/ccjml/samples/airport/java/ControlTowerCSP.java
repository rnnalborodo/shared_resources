package es.upm.babel.ccjml.samples.airport.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;
//@ model import org.jcsp.lang.AltingChannelInput;

/** ControlTower implementation using CSP. 
 * 
 * @author Babel Group
 */ 
public class ControlTowerCSP extends AControlTower implements CSProcess {

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
    //@assume runways[r] && r >=0 && r < runways.length;
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
    //@ assume runways[r] && r >=0 && r < runways.length;
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
    syncCond[AFTER_LANDING] = true;
    syncCond[AFTER_TAKEOFF] = true;

    while (true) {
      syncCond[BEFORE_LANDING] = cpreBeforeLanding();
      syncCond[BEFORE_TAKEOFF] = cpreBeforeTakeOff() ;
      
      /*@ assert 
        @   syncCond[BEFORE_LANDING] == cpreBeforeLanding() &&
        @   syncCond[BEFORE_TAKEOFF] == cpreBeforeTakeOff() &&
        @   syncCond[AFTER_LANDING] &&
        @   syncCond[AFTER_TAKEOFF] ;
        @*/

      chosenService = services.fairSelect(syncCond);
      /*@ assume chosenService < guards.length && chosenService >= 0 && 
        @        ((AltingChannelInput) guards[chosenService]).pending() &&
        @        syncCond[chosenService];
        @*/
      
      switch(chosenService){
        case BEFORE_LANDING:
          //@ assert cpreBeforeLanding();
          innerCh = (One2OneChannel) chBeforeLanding.in().read();
          innerCh.out().write(this.getRunway());
          break;
  
        case BEFORE_TAKEOFF:
          //@ assert cpreBeforeTakeOff();
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

  /*@ public normal_behaviour
    @    requires cpreBeforeLanding() && true && repOk();
    @    assignable runways[*];
    @    ensures \result < runways.length && \result >= 0 && runways[\result] &&
    @            (\forall int i; i >= 0 && i < runways.length; runways[i] == \old(runways)[i] || i == \result);
    @*/
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