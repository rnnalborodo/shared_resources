package es.upm.babel.ccjml.samples.airport.java;

/**
 * Pre and Cpre definitions for the Control Tower Problem 
 * 
 * @author raul.alborodo
 *
 */
public abstract class AControlTower implements ControlTower {

  //@ public represents runs <- runways;
  protected /*@ spec_public @*/ boolean runways[];

  /*@ public normal_behavior
    @   ensures \result == (\exists int i; i >= 0 && i < runways.length; runways[i]);
    @*/
  public /*@ pure @*/ boolean cpreBeforeLanding(){
    return cpreBefore();
  }

  /*@ public normal_behavior
    @   ensures \result == (\exists int i; i >= 0 && i < runways.length; runways[i]);
    @*/
  public /*@ pure @*/ boolean cpreBeforeTakeOff(){
    return cpreBefore();
  }

  /*@ private normal_behavior
    @   ensures \result == (\exists int i; i >= 0 && i < runways.length; runways[i]);
    @*/
  private /*@ pure @*/ boolean cpreBefore(){
    for (int i = 0; i < runways.length; i++) {
      if (!runways[i]){
        return true;
      }
    }
    return false;
  }


  /*@ private normal_behavior
    @   requires r >=0 && r < runways.length;
    @   ensures runways[r]; 
    @*/
  private /*@ pure @*/ boolean preAfter(int r){
    return runways[r] && r >=0 && r < runways.length;
  }

  /*@ protected normal_behavior
    @   requires r >=0 && r < runways.length;
    @   ensures runways[r]; 
    @*/
  protected /*@ pure @*/ boolean preAfterLanding(int r){
    return preAfter(r);
  }

  /*@ protected normal_behavior
    @   requires r >=0 && r < runways.length;
    @   ensures runways[r]; 
    @*/
  protected /*@ pure @*/ boolean preAfterTakeOff(int r){
    return preAfter(r);
  }
  
  /*@ public normal_behavior
    @   ensures true;
    @*/ 
  public /*@ pure @*/ boolean repOk(){
    return true;
  }

  
}
