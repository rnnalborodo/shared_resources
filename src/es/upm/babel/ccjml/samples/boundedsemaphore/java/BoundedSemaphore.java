package es.upm.babel.ccjml.samples.boundedsemaphore.java;

public interface /*@ shared_resource @*/ BoundedSemaphore {
  //@ public model instance int value;
  //@ public model instance int bound;

  //@ public instance invariant value >= 0 && value <= bound;
  //@ public instance invariant 0 < bound;

  //@ public initially value == 0;

  // public normal_behaviour
  //  ensures bound == _bound;
  //  public BoundedSemaphore(int _bound);

  //@ public normal_behaviour
  //@   cond_sync value < bound;
  //@   ensures value == \old(value) + 1;
  public void v();

  //@ public normal_behaviour
  //@   cond_sync value > 0;
  //@   ensures value == \old(value) - 1;
  public void p();
}