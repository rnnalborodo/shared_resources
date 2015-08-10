package es.upm.babel.ccjml.samples.airport.java.key;

import es.upm.babel.ccjml.samples.csp.JCSPKeY;
import es.upm.babel.ccjml.samples.csp.list.src.List;

/** ControlTower implementation using CSP. KeY Instrumentation 
 * 
 * @author Babel Group
 */ 
public class ControlTowerCSPKeY {

  //@ public invariant runways.length > 0;
  private /*@ spec_public @*/boolean runways[];

  private /*@ spec_public @*/List runwaysInUse;

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
  //@ public invariat chBeforeLanding >=0;
  private int chBeforeLanding;
  //@ public invariat chBeforeTakeOff >=0;
  private int chBeforeTakeOff;
  //@ public invariat chAfterLanding >=0;
  private int chAfterLanding;
  //@ public invariat chAfterTakeOff >=0;
  private int chAfterTakeOff;

  /** SERVER IMPLEMENTATION */
  /**
   * Constants representing the method presented in the API
   */
  private static final int BEFORE_LANDING = 0;
  private static final int BEFORE_TAKEOFF = 1;
  private static final int AFTER_LANDING = 2;
  private static final int AFTER_TAKEOFF = 3;

  /** Auxiliary variables to express 'assume' constraints as verifiable by KeY */
  //  explain each of the and why is that generally
  // safety
  private boolean wellFormedGuards;
  private boolean wellFormedSyncCond;
  private boolean propEffectiveFairSelect;
  private boolean propSafeSelection;
  
  /*@ requires chBeforeLanding +
    @          chBeforeTakeOff +
    @          chAfterLanding +
    @          chAfterTakeOff > 0;
    @*/
  //@ assignable wellFormedGuards, wellFormedSyncCond, propEffectiveFairSelect;
  //@ assignable propSafeSelection;
  //@ assignable runways[*];
  //@ ensures wellFormedGuards && wellFormedSyncCond;
  //@ ensures propEffectiveFairSelect;
  //@ ensures propSafeSelection;
  public void serverInstance() {
    /** Init the variables as false like basic case */
    wellFormedGuards = true;
    wellFormedSyncCond = true;
    propSafeSelection = true;
    propEffectiveFairSelect = true;
    
    /** One entry for each method */
    int[] guards = {
        chBeforeLanding,
        chBeforeTakeOff,
        chAfterLanding,
        chAfterTakeOff
    };

    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean syncCond[] = new boolean[4];
    int chosenService = 0;

    while (chosenService != -1 ) {
      syncCond[BEFORE_LANDING] = cpreBeforeLanding();
      syncCond[BEFORE_TAKEOFF] = cpreBeforeTakeOff() ;
      syncCond[AFTER_LANDING] = true;
      syncCond[AFTER_TAKEOFF] = true;
      //@ assert syncCond is consistent,i.e, all refreshments are done properly

      wellFormedSyncCond &= 
          (!syncCond[BEFORE_LANDING] || cpreBeforeLanding()) &&
          (!syncCond[BEFORE_TAKEOFF] || cpreBeforeTakeOff()) &&
          (!syncCond[AFTER_LANDING] || true) &&
          (!syncCond[AFTER_TAKEOFF] || true) &&
          syncCond.length == 4;
      
      chosenService = JCSPKeY.fairSelect(syncCond, guards);
      propEffectiveFairSelect &= 
          chosenService < guards.length && chosenService >= 0 &&
          guards[chosenService] > 0 &&
          syncCond[chosenService];
      
      switch(chosenService){
        case BEFORE_LANDING:
          propSafeSelection&= cpreBeforeLanding();
          guards[BEFORE_LANDING]--;
          this.getRunway();
          break;
  
        case BEFORE_TAKEOFF:
          propSafeSelection&= cpreBeforeTakeOff();
          guards[BEFORE_TAKEOFF]--;
          runwaysInUse.add(this.getRunway());
          break;
  
        case AFTER_LANDING: 
          propSafeSelection&= true;
          guards[AFTER_LANDING]--;
          int r = (int) runwaysInUse.get(0);
          runways[r] = false;
          runwaysInUse.remove(r);
          break;
  
        case AFTER_TAKEOFF:
          propSafeSelection&= true;
          guards[AFTER_TAKEOFF]--;
          int r1 = (int) runwaysInUse.get(0);
          runways[r1] = false;
          runwaysInUse.remove(r1);
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