package es.upm.babel.ccjml.samples.recyclingplant.java;

import java.util.HashMap;
import java.util.Map;

import es.upm.babel.ccjml.samples.recyclingplant.java.runenv.Crank;
import es.upm.babel.cclib.Monitor;

/**
 * @author rnnalborodo
 */
public class RecyclingPlantMonitor implements RecyclingPlant{

  private int MAX_W_CONTAINER;
  private final int MAX_CRANES = Crank.MAX_CRANKS;
  
  private int weight;
  private State state;
  private int accessing;
  
  private Monitor mutex;
  private Map<Integer,Monitor.Cond> cranes;
  private Monitor.Cond cranesNotifying;
  private Monitor.Cond full;
 
  
  public RecyclingPlantMonitor(){
    this(10);
  }
  
  public RecyclingPlantMonitor(int max){
    MAX_W_CONTAINER = max; 
    weight = 0;
    state = State.READY;
    accessing = 0;
    
    mutex = new Monitor();
    cranesNotifying = mutex.newCond();
    cranes = new HashMap<>(); // ConcurrentHashMap is not needed due to the use of Monitors
    full = mutex.newCond();
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
  private boolean cprePrepareReplacement() {
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
  public void notifyWeight(int w){
    mutex. enter();
    if (!cpreNotifyWeight()) {
      cranesNotifying.await(); 
    }
    
    //@ assume cpreNotifyWeight(w);
    if (weight + w > MAX_W_CONTAINER ) {
      state = State.TO_REPLACE;
    } else {
      state = State.READY;
    }
    
    unblobckingCode();
  
    mutex.leave();
  }
  
  //@ public normal_behaviour 
  //@   requires w > 0;
  //@   cond_sync weight + w <= MAX && state != State.REPLACING;
  //@   assignable weight;
  //@   ensures weight == \old(weight) + w && accessing = \old(accessing)+1;
  @Override
  public void incrementWeight(int w){
    mutex. enter();

    if (!cpreIncrementWeight(w)) {
      if (!cranes.keySet().contains(w)) {
        cranes.put(w, mutex.newCond());
      }
      cranes.get(w).await();
    }
    
    //@ assume cpreIncrementWegith(w);
    accessing ++;
    weight += w;
    
    unblobckingCode();

    mutex.leave();
  }
  
  
  //@ public normal_behaviour 
  //@   assignable accessing;
  //@   ensures accessing == \old(accessing) -1;
  @Override
  public void notifyDrop(){
    mutex.enter();
    accessing--;
    
    //@ assume cpreNotifyDrop();
    unblobckingCode();
    
    mutex.leave();
  }
  
  //@ public normal_behaviour
  //@   cond_sync state == State.TO_REPLACE && accessing == 0;
  //@   assignable state;
  //@   ensures state == State.REPLACING;
  @Override
  public void prepareReplacement(){
    mutex. enter();
    if (!cprePrepareReplacement()) {
      full.await();
    }
    
    //@ assume cprePrepareReplacement();
    state = State.REPLACING;
    
    // no waking up could be done!    
    mutex.leave();
  }
  
  //@ public normal_behaviour
  //@   requires state == State.REPLACING && accessing == 0 && max > 0;
  //@   assignable weight, state, MAX_W_CONTAINER;
  //@   ensures weight == 0 && state == State.READY && MAX_W_CONTAINER = max;
  @Override
  public void notifyReplacement(int max){
    mutex.enter();
    
    //@ assume cpreNotifyReplacement();
    MAX_W_CONTAINER = max;
    weight = 0;
    state = State.READY;
    
    unblobckingCode();
    
    mutex.leave();
  }
  
  private synchronized void unblobckingCode(){
    // --   Waking up code
    // wake up any crane with less steel than the available room
    // optimizing container before replacing it
    boolean craneAvailable = false;
    for (int i = MAX_W_CONTAINER - weight; i > 0 && !craneAvailable; i--) {
      if (cranes.keySet().contains(i) && cranes.get(i).waiting()> 0) {
        cranes.get(i).signal();
        craneAvailable = true;
      }
    }
    // if there is no wainting crane with less weight that then available
    // try to notify first
    // then replace the container if any
    if (state == State.TO_REPLACE && ! craneAvailable) {
      if (accessing == 0 && full.waiting() > 0) {
        full.signal();
      } else {
        // state allows any crane to notify the access
        if (cranesNotifying.waiting() > 0) {
          cranesNotifying.signal();
        }
      }
    }
  }
}
