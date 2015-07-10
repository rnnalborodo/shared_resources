 package es.upm.babel.ccjml.samples.boundedsemaphore.java.key;

/**
 * Semaphore implementation using JCSP Library with channel expansion. 
 * KeY Instrumentation.
 *
 * @author BABEL Group
 */
public class BoundedSemaphoreCSPKeY {
  
  //@ requires (syncCond.length == guards.length);
  /*@ ensures (\result >= 0 && \result < syncCond.length && 
    @          syncCond[\result] && guards[\result] > 0 )
    @         ||
    @         (\result == -1 &&
    @           (\forall int i; i >= 0 && i < syncCond.length; 
    @                           !syncCond[i] || guards[i] == 0)
    @         );
    @*/
  public static int /*@ pure @*/ fairSelect(boolean[] syncCond, int[] guards){
    for(int i = 0 ; i < syncCond.length; i++){
      if (syncCond[i] && guards[i] > 0)
        return i;
    }
    return -1;
  }
  
  /** SHARED RESOURCE IMPLEMENTATION */
  //@ public instance invariant value >= 0 && value <= bound;
  //@ public instance invariant 0 < bound;

  //@ public initially value == 0;
  
  private int value;
  private int bound;
  
  /** WRAPPER IMPLEMENTATION */
  //@ensures \result == value < bound;
  private boolean cpreV(){
    return value < bound;
  }
  
  //@ensures \result == value > 0;
  private boolean cpreP(){
    return value > 0;
  }
  
  /** Channel for receiving external request for each method */
  //@ public invariant ch_v >=0;
  private int ch_v;
  //@ public invariant ch_v >=0;
  private int ch_p;
  
  /** SERVER IMPLEMENTATION */
  /** Constants representing the method presented in the API */
  final int V = 0;
  final int P = 1;

  /** Auxiliary variables to express 'assume' constraints as verifiable by KeY */
  //  explain each of the and why is that generally
  // safety
  private boolean wellFormedGuards;
  private boolean wellFormedSyncCond;
  private boolean propEffectiveFairSelect;
  private boolean propSafeSelection;
  
  /*@ requires ch_p +
    @          ch_v > 0;
    @*/
  /*@ requires ch_p +
    @          ch_v <= 2;
    @*/
  //@ assignable wellFormedGuards, wellFormedSyncCond, propEffectiveFairSelect;
  //@ assignable propSafeSelection;
  //@ ensures wellFormedGuards && wellFormedSyncCond;
  //@ ensures propEffectiveFairSelect;
  //@ ensures propSafeSelection;
  public void serverInstance() {
    /** Init the variables as false like basic case */
    wellFormedGuards = true;
    wellFormedSyncCond = true;
    propSafeSelection = true;
    propEffectiveFairSelect = true;
    
    int[] guards = {
      ch_v,
      ch_p
    };

    /** Conditional reception for fairSelect(). */
    boolean syncCond[] = new boolean[2];
    //@ assume syncCond.length == 2;

    int chosenService = 0;
    
    while (chosenService != -1) {
      // refreshing synchronization conditions
      syncCond[V] = this.value < this.bound;
      syncCond[P] = this.value > 0;
      wellFormedSyncCond &= (!syncCond[V] || cpreV());
      wellFormedSyncCond &= (!syncCond[P] || cpreP());
      wellFormedSyncCond &= (syncCond.length == 2);

      chosenService = fairSelect(syncCond,guards);

      switch(chosenService){
        case V: 
          propSafeSelection &= true && cpreV();
          innerV();
          guards[V]--;
          break;

        case P:
          propSafeSelection &= true && cpreP();
          innerP();
          guards[P]--;
      }
    }
  }

  //@ public normal_behaviour
  //@   requires value > 0;
  //@   ensures value == \old(value) + 1;
  private void innerV() {
    value++;
  }
  
  //@ public normal_behaviour
  //@   requires value > 0;
  //@   ensures value == \old(value) - 1;
  private void innerP(){
    value--;
  }
}
