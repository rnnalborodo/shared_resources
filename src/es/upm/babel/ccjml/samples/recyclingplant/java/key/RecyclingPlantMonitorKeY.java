package es.upm.babel.ccjml.samples.recyclingplant.java.key;

/**
 * @author rnnalborodo
 */
public class RecyclingPlantMonitorKeY{

  // Class members
  /*@ public invariant
    @  MAX == 2;
    */
  public static final int MAX = 2;

  // Instance members: shared resource internal state
  private /*@ spec_public @*/ int MAX_W_CONTAINER;
  private /*@ spec_public @*/int MAX_CRANES;
  private /*@ spec_public @*/int weight;
  
  //@ public instance invariant weight > 0 && weight <= MAX_W_CONTAINER;
  //@ public instance invariant accessing > 0 && accessing <= MAX_CRANES;
  //@ public instance invariant MAX_CRANES > 0 && MAX_W_CONTAINER > 0;
  
  public static enum State { READY, TO_REPLACE, REPLACING }
  private State state;
  
  //@ public invariant accessing >= 0; 
  private int accessing;
  
  private int[] cranes = new int[MAX];
  //@ public invariant cranesNotifying >= 0; 
  private int cranesNotifying;
  //@ public invariant full >= 0; 
  private int full;
  
  // prop_0_1_signal depicted as an invariant
  //@ public invariant signaled >= 0 && signaled <= 1;
  private /*@ spec_public @*/int signaled  = 0;

  //@ requires w > 0;
  //@ ensures \result == (weight + w <= MAX_W_CONTAINER && state != State.REPLACING);
  private boolean cpreIncrementWeight(int w){
    return weight + w <= MAX_W_CONTAINER && state != State.REPLACING;
  } 
  
  // requires w > 0;
  //@ ensures \result == state != State.REPLACING;
  private boolean cpreNotifyWeight(){
    return state != State.REPLACING;
  }
  
  //@ ensures \result == (state == State.TO_REPLACE && accessing == 0);
  private boolean cprePrepareReplacement() {
    return state == State.TO_REPLACE && accessing == 0;
  }
   
  //@ assignable full, cranesNotifying, signaled;
  //@ assignable weight, accessing, state;
  //prop_safe_signal
  /*@ ensures
    @  (
    @        (full + 1 == \old(full) ==> cprePrepareReplacement() )
    @        &&
    @        (cranesNotifying + 1 == \old(cranesNotifying) ==> cpreNotifyWeight())
    @  );
    @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @       full + 1 == \old(full) ||
    @       cranesNotifying + 1 == \old(cranesNotifying)
    @  );
    @*/  
 // prop_liveness
  /*@ ensures (
     @       (\old(full) > 0 && cprePrepareReplacement()) ||
     @       (\old(cranesNotifying) > 0 && cpreNotifyWeight()) || true
     @  ) 
     @  ==>
     @    signaled == 1;
     @*/
  // prop_signal_and_return
  /*@ ensures 
    @         weight == \old(weight) && accessing == \old(accessing) &&
    @         state == \old(state) ;
    @*/
  private synchronized void unblobckingCode(){
    boolean craneAvailable = false;
    signaled = 0;
//    for (int i = MAX_W_CONTAINER - weight; i > 0 && !craneAvailable; i--) {
//      if (cranes.entrySet().contains(i) && cranes.get(i).waiting()> 0) {
//        cranes.get(i).signal();
//        craneAvailable = true;
//      }
//    }
    // if there is no wainting crane with less weight that then available
    // try to notify first
    // then replace the container if any
    if (state == State.TO_REPLACE && !craneAvailable)
      if (accessing == 0 && full > 0) {
        full--;
        signaled++;
      } else {
        // state allows any crane to notify the access
        if (cranesNotifying > 0 ) {
          if (cpreNotifyWeight()){
            cranesNotifying--;
            signaled++;
          }
          
        }
      }
  }
}
