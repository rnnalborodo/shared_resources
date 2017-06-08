package es.upm.babel.ccjml.samples.airport.java.key;

import es.upm.babel.key.cclib.MonitorKey;

/** 
 * ControlTower (instrumented) implementation using Priority Monitors
 * 
 * @author raul.alborodo
 */ 
public class ControlTowerMonitorKeY {

  //@ public ghost int awakenThread;

  private /*@ spec_public @*/ boolean runways[];

  private /*@ spec_public @*/ MonitorKey.Cond waitingPlanes;

  //@ ensures \result == true  ==> (\exists int i; i >= 0 && i < runways.length; runways[i]);
  protected /*@ pure @*/ boolean cpreBeforeLanding(){
    return cpreBefore();
  }

  //@ ensures \result == (\exists int i; i >= 0 && i < runways.length; runways[i]);
  protected /*@ pure @*/ boolean cpreBeforeTakeOff(){
    return cpreBefore();
  }

  //@ ensures \result == (\exists int i; i >= 0 && i < runways.length; runways[i]);
  private /*@ spec_public pure @*/ boolean cpreBefore(){
    boolean found = false;
    /*@ loop_invariant
      @   i >= 0 && i<= runways.length &&
      @     (found ==> (\exists int j; j >=0 && j< i ; runways[j]))
      @ ;  
      @*/
    for (int i = 0; i < runways.length; i++) {
      if (!runways[i]){
        found = true;
        break;
      }
    }
    return found;
  }

  //@ requires r >=0 && r < runways.length;
  //@ ensures runways[r]; 
  protected /*@ pure @*/ boolean preBeforeLanding(int r){
    return runways[r] && r >=0 && r < runways.length;
  }

  //@ requires r >=0 && r < runways.length;
  //@ ensures runways[r]; 
  protected /*@ pure @*/ boolean preBeforeTakeOff(int r){
    return runways[r] && r >=0 && r < runways.length;
  }

  protected /*@ spec_public @*/ int signaled;

  //@ requires cpreBefore();
  //@ assignable signaled, waitingPlanes;
  //prop_safe_signal
  /*@ ensures 
    @        (waitingPlanes.waiting() + 1 == \old(waitingPlanes).waiting() ==> cpreBefore())
    @  ;
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @        waitingPlanes.waiting() == \old(waitingPlanes).waiting() || 
    @        waitingPlanes.waiting() +1 == \old(waitingPlanes).waiting()
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @        waitingPlanes.waiting() + 1 == \old(waitingPlanes).waiting() 
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  (awakenThread != -1 &&
    @    (
    @      (waitingPlanes.waiting() >0 && cpreBefore())
    @    )
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
  // prop_signal_and_return - nothing to do here
  protected void unblobckingCode(){
    // Second step using Model Search as Aritmetic Treatment
    //@ set awakenThread = -1; 
    signaled = 0; 
    if (waitingPlanes.waiting() > 0) {
      waitingPlanes.signal();
      //@ set awakenThread = 0;
      //@ assert cpreBefore();
      signaled ++;
    }
  }
}