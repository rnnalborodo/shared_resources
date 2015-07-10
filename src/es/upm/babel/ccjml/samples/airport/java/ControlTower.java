package es.upm.babel.ccjml.samples.airport.java;

/** 
 * @author Babel Group 
 */

public interface /*@ shared_resource @*/ ControlTower { 
  
  //@ public model instance JMLObjectSequence data;

  //@ public instance invariant MAX > 0;
  //@ public instance invariant data.length() <= MAX;

  //@ public initially data.length() == 0;
  //@ public initially MAX > 0;

  //@ public normal_behaviour
  //@   requires true;
  //@   cond_sync data.length <= MAX - 1;
  //@   assignable data;
  //@   ensures data == \old(data).insertBack(n);
  
  public int beforeLanding();
  public void afterLanding(int r);
  public int beforeTakeOff();
  public void afterTakeOff(int r);

}
