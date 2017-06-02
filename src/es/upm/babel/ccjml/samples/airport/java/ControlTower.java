package es.upm.babel.ccjml.samples.airport.java;

/** 
 * Airport Traffic Control Tower with several runs.
 * 
 * @author raul.alborodo
 */

public interface /*@ shared_resource @*/ ControlTower { 
  
  //@ public instance model non_null boolean[] runs;

  //@ public instance invariant runs.length <= runs.length;

  //@ public initially (\forall int i ; i >=0 && i<runs.length; !runs[i]);

  /*@ public normal_behaviour
    @   requires true;
    @   cond_sync (\exists int i ; i >=0  && i < runs.length ; !runs[i]);
    @   assignable runs[*];
    @   ensures \result < runs.length && \result >=0 && runs[\result] &&
    @           (\forall int i; i>=0 && i< runs.length && i != \result; 
    @                                           runs[i] == \old(runs[i]));
    @*/
  public int beforeLanding();
  
  /*@ public normal_behaviour
    @   requires runs[r] && r >= 0 && r < runs.length;
    @   cond_sync true;
    @   assignable runs;
    @   ensures !runs[r];
    @*/
  public void afterLanding(int r);
  
  /*@ public normal_behaviour
    @   requires true;
    @   cond_sync (\exists int i ; i >=0  && i < runs.length ; !runs[i]);
    @   assignable runs[*];
    @   ensures \result < runs.length && \result >=0 && runs[\result] &&
    @           (\forall int i; i>=0 && i< runs.length && i != \result; 
    @                                           runs[i] == \old(runs[i]));
    @*/
  public int beforeTakeOff();
  
  /*@ public normal_behaviour
    @   requires runs[r] && r >= 0 && r < runs.length;
    @   cond_sync true;
    @   assignable runs[r];
    @   ensures !runs[r];
    @*/
  public void afterTakeOff(int r);

}
