package es.upm.babel.ccjml.samples.airport.java;

public abstract class AControlTower implements ControlTower {

  //@ public invariant runways.length == monitors.length;
  protected /*@ spec_public @*/boolean runways[];

  //@ ensure \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  protected /*@ pure @*/ boolean cpreBeforeLanding(){
    return cpreBefore();
  }

  //@ ensure \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  protected /*@ pure @*/ boolean cpreBeforeTakeOff(){
    return cpreBefore();
  }

  //@ ensure \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  private /*@ pure @*/ boolean cpreBefore(){
    for (int i = 0; i < runways.length; i++) {
      if (!runways[i]){
        return true;
      }
    }
    return false;
  }

  //@ requires r >=0 && r < runways.length;
  //@ ensure runways[r]; 
  private /*@ pure @*/ boolean preBefore(int r){
    return runways[r] && r >=0 && r < runways.length;
  }
  
  //@ requires r >=0 && r < runways.length;
  //@ ensure runways[r]; 
  protected /*@ pure @*/ boolean preBeforeLanding(int r){
    return preBefore(r);
  }

  //@ requires r >=0 && r < runways.length;
  //@ ensure runways[r]; 
  protected /*@ pure @*/ boolean preBeforeTakeOff(int r){
    return preBefore(r);
  }
  
  /*@ public normal_behavior
    @   ensures true;
    @*/ 
  protected /*@ pure @*/ boolean repOk(){
    return true;
  }

  
}
