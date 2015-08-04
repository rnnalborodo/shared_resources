package es.upm.babel.ccjml.samples.recyclingplant.java;

/**
 * @author rnnalborodo
 */
public interface /*@ shared_resource @*/RecyclingPlant {

  public static enum State { READY, TO_REPLACE, REPLACING }

  //@ public model instance int MAX_CRANES;
  //@ public model instance int MAX_W_CONTAINER;
  //@ public model instance int weight;
  //@ public model instance State state;
  //@ public model instance int accessing;
  
  //@ public instance invariant weight > 0 && weight <= MAX_W_CONTAINER;
  //@ public instance invariant accessing > 0 && accessing <= MAX_CRANES;
  //@ public instance invariant MAX_CRANES > 0 && MAX_W_CONTAINER > 0;
  
  //@ public normal_behaviour 
  //@   requires w > 0;
  //@   cond_sync state != State.REPLACING;
  //@   assignable state;
  /*@   ensures (weight + w > MAX_W_CONTAINER && state == State.TO_REPLACE) ||
    @                (weight + w <= MAX_W_CONTAINER && state == State.READY);
    @*/
  public void notifyWeight(int w);
  
  //@ public normal_behaviour 
  //@   requires w > 0;
  //@   cond_sync weight + w <= MAX_W_CONTAINER && state != State.REPLACING;
  //@   assignable weight, accessing;
  //@   ensures weight == \old(weight) + w && accessing == \old(accessing)+1;
  public void incrementWeight(int w);
  
  
  //@ public normal_behaviour 
  //@   assignable accessing;
  //@   ensures accessing == \old(accessing) -1;
  public void notifyDrop();
  
  //@ public normal_behaviour
  //@   cond_sync state == State.TO_REPLACE && accessing == 0;
  //@   assignable state;
  //@   ensures state == State.REPLACING;
  public void prepareReplacement();
  
  //@ public normal_behaviour
  //@   requires state == State.REPLACING && accessing == 0 && max > 0;
  //@   assignable weight, state, MAX_W_CONTAINER;
  //@   ensures weight == 0 && state == State.READY && MAX_W_CONTAINER == max;
  public void notifyReplacement(int max);
  
}
