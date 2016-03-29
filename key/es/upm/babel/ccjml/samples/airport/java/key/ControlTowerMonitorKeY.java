package es.upm.babel.ccjml.samples.airport.java.key;

/** 
 * ControlTower (instrumented) implementation using Priority Monitors
 * 
 * @author BABEL Group - Technical University of Madrid
 */ 
public class ControlTowerMonitorKeY {

  //@ ghost int awakenThread;

  //@ public invariant runways.length > 0;
  private /*@ spec_public @*/boolean runways[];
  //@ public invariant waitingPlanes > 0;
  private /*@ spec_public @*/ int waitingPlanes;

  //@ ensures \result == true  ==> (\exists int i; i >= 0 && i < runways.length; runways[i]);
  private /*@ pure @*/ boolean cpreBeforeLanding(){
    return cpreBefore();
  }

  //@ ensures \result == (\exists int i; i >= 0 && i < runways.length; runways[i]);
  private /*@ pure @*/ boolean cpreBeforeTakeOff(){
    return cpreBefore();
  }

  //@ ensures \result == (\exists int i; i >= 0 && i < runways.length; runways[i]);
  private /*@ pure @*/ boolean cpreBefore(){
    boolean found = false;
    /*@ loop_invariant
      @   i >= 0 && i<= runways.length &&
      @     (\forall int j; j >=0 && j< i ; !runways[j]) &&
      @     found ==> runways[i]
      @ ;  
      @*/
    for (int i = 0; i < runways.length && !found; i++) {
      if (!runways[i]){
        found = true;
      }
    }
    return found;
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

  private /*@ spec_public @*/ int signaled;

  //@ requires cpreBefore();
  //@ assignable signaled, waitingPlanes;
  //prop_safe_signal
  /*@ ensures 
    @        (waitingPlanes + 1 == \old(waitingPlanes) ==> cpreBefore())
    @  ;
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @        waitingPlanes == \old(waitingPlanes) || 
    @        waitingPlanes +1 == \old(waitingPlanes)
    @  ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @        waitingPlanes + 1 == \old(waitingPlanes) 
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  (awakenThread != -1 &&
    @    (
    @      (waitingPlanes >0 && cpreBefore())
    @    )
    @  ) ==>
    @    signaled == 1
    @  ;
    @*/
  // prop_signal_and_return - nothing to do here
  private void unblobckingCode(){
    // Second step using Model Search as Aritmetic Treatment
    //@ set awakenThread = -1; 
    signaled = 0; 
    if (waitingPlanes > 0) {
      waitingPlanes--;
      //@ set awakenThread = 0;
      //@ assert cprePut(i);
      signaled ++;
    }
  }
}