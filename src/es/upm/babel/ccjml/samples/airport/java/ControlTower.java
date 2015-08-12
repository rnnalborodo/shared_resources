package es.upm.babel.ccjml.samples.airport.java;

/** 
 * Airport Traffic Control Tower with several runways.
 * 
 * @author Babel Group 
 */

public interface /*@ shared_resource @*/ ControlTower { 
  
  //@ public model instance JMLObjectSequence data;
  //@ public model instance int MAX;

  //@ public instance invariant MAX > 0;
  //@ public instance invariant data.length() <= MAX;
  //@ public invariant (\forall int i : i >=0  && i <MAX : \typeof(data.get(i)) == Boolean);

  //@ public initially  (\forall int i : i >=0  && i <MAX : !data.get(i));
  //@ public initially data.length() == MAX;
  //@ public initially MAX > 0;

  //@ public normal_behaviour
  //@   requires true;
  //@   cond_sync (\exist int i : i >=0  && i < MAX : !data.get(i));
  //@   assignable data;
  //@   ensures \result < MAX && \result >=0 && data.get(\result);
  public int beforeLanding();
  
  //@ public normal_behaviour
  //@   requires data.get(r) && r >= 0 && r < MAX;
  //@   cond_sync true;
  //@   assignable data;
  //@   ensures !data.get(r);
  public void afterLanding(int r);
  
  //@ public normal_behaviour
  //@   requires true;
  //@   cond_sync (\exist int i : i >=0  && i < MAX : !data.get(i));
  //@   assignable data;
  //@   ensures \result < MAX && \result >=0 && data.get(\result);
  public int beforeTakeOff();
  
  //@ public normal_behaviour
  //@   requires data.get(r) && r >= 0 && r < MAX;
  //@   cond_sync true;
  //@   assignable data;
  //@   ensures !data.get(r);
  public void afterTakeOff(int r);

}
