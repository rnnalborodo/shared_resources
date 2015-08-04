package es.upm.babel.ccjml.samples.recyclingplant.java;

import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * @author rnnalborodo
 */
public class RecyclingPlantSync implements RecyclingPlant{

  private  int MAX_W_CONTAINER;
  
  private int weight;
  private State state;
  private int accessing;
  
  public RecyclingPlantSync(){
    this(10);
  }
  
  public RecyclingPlantSync(int max){
    MAX_W_CONTAINER = max;
    weight = 0;
    state = State.READY;
    accessing = 0;
  }
  
  //@ requires w > 0;
  //@ ensures \result == (weight + w <= MAX_P_CONTAINER && state != State.REPLACING);
  private boolean cpreIncrementWeight(int w){
    return weight + w <= MAX_W_CONTAINER && state != State.REPLACING;
  }
  
  //@ requires w > 0;
  //@ ensures \result == state != State.REPLACING;
  private boolean cpreNotifyWeight(){
    return state != State.REPLACING;
  }
  
  //@ ensures \result ==state == State.TO_REPLACE && accessing == 0;
  private boolean cprePreparingReplacement() {
    return state == State.TO_REPLACE && accessing == 0;
  }
  
  //@ public normal_behaviour 
  //@   requires w > 0;
  //@   cond_sync state != State.REPLACING;
  //@   assignable state;
  /*@   ensures (weight + w > MAX_W_CONTAINER && state = State.TO_REPLACE) ||
     @                (weight + w <= MAX_W_CONTAINER && state = State.READY);
     @*/
  @Override
  public synchronized void notifyWeight(int w){
    while (!cpreNotifyWeight()) {
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(RecyclingPlantSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    }

    if (weight + w > MAX_W_CONTAINER ) {
      state = State.TO_REPLACE;
      } else {
      state = State.READY;
    }

    notifyAll();
  }
  
  //@ public normal_behaviour 
  //@   requires w > 0;
  //@   cond_sync weight + w <= MAX && state != State.REPLACING;
  //@   assignable weight;
  //@   ensures weight == \old(weight) + w;
  @Override
  public synchronized void incrementWeight(int w){
    while (!cpreIncrementWeight(w)) {
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(RecyclingPlantSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    }
    accessing++;
    weight += w;
    
    notifyAll();
  }
  
  
  //@ public normal_behaviour 
  //@   requires accessing > 0;
  //@   assignable accessing;
  //@   ensures accessing == \old(accessing) -1;
  @Override
  public synchronized void notifyDrop(){
    accessing--;
    notifyAll();
  }
  
  //@ public normal_behaviour
  //@   cond_sync state == State.TO_REPLACE && accessing == 0;
  //@   assignable state;
  //@   ensures state == State.REPLACING;
  @Override
  public synchronized void prepareReplacement(){
    while (!cprePreparingReplacement()) {
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(RecyclingPlantSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    }
    
    state = State.REPLACING;
    // no waking up could be done!
  }
  
  //@ public normal_behaviour
  //@   requires state == State.REPLACING && accessing == 0;
  //@   assignable weight, state, MAX_W_CONTAINER;
  //@   ensures weight == 0 && state == State.READY && MAX_W_CONTAINER > 0;
  @Override
  public synchronized void notifyReplacement(int max){
    
    MAX_W_CONTAINER = max;
    weight = 0;
    state = State.READY;
    
    notifyAll();
  }
  
}
