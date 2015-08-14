package es.upm.babel.ccjml.samples.multibuffer.java;

import es.upm.babel.cclib.Monitor;

/** 
 * Multibuffer implementation using monitors and conditions.
 *
 * @author BABEL Group
 */
public class MultibufferMonitor extends AMultibuffer {
  
  /** Guarantee mutual exclusion in critic sections */
  private final Monitor mutex;
  private final Monitor.Cond[] emptiness;
  private final Monitor.Cond[] fullness;
  
  //@ public normal_behaviour
  //@ ensures \result == maxData > 0 && data.length() <= MAX;
  //@ public model pure boolean invariant();
  public MultibufferMonitor(int m) {
    MAX = m;
    this.nData = 0;
    this.buffer = new Object[m];
    this.first = 0;

    // initialization of concurrent elements
    this.mutex = new Monitor();
    this.emptiness = new Monitor.Cond[m+1];
    for (int i = 1; i < emptiness.length; i++) {
      emptiness[i]= mutex.newCond();
    }
    
    this.fullness = new Monitor.Cond[m+1];
    for (int i = 1; i < fullness.length; i++) {
      fullness[i]= mutex.newCond();
    }
  }
  
  @Override
  public void put(Object[] els) {
    //@assume els.length <= MAX / 2;
    mutex.enter();

    if (els.length > MAX - nData) {
      emptiness[els.length].await();
    }
    
    //@ assert (els.length <= MAX / 2) && (els.length <= nSlots());
    for (Object el : els) {
      buffer[(first + nData) % MAX] = el;
      nData++;
    }
    unblockingCode();
    mutex.leave();
  }

  @Override
  public Object[] get(int n) {
    mutex.enter();
    //@ assume (n <= MAX / 2);
    if (nData < n){
      fullness[n].await();
    }
    
    //@ assert (n <= MAX / 2) && n <= nData();
    Object[] gotData = new Object[n];
    for (int i = 0; i < n; i++) {
      gotData[i] = buffer[first];
      buffer[first] = null;
      first++;
      first %= MAX; 
      nData--;
    }
    unblockingCode();
    mutex.leave();
    return gotData;
  }

  private int signaled;
  //@ requires true;
  //@ assignable emptiness[*], fullness[*];
  /*@ ensures 
    @   (\forall int i; i>=1 && i < MAX + 1; 
    @     emptiness[i] == \old(emptiness[i]) && fullness[i]==\old(fullness[i]))
    @   ||
    @   (\exists int i; i>=1 && i < MAX + 1;
    @     (emptiness[i] != \old(emptiness)[i] &&
    @          && fullness[i] == \old(fullness)[i])
    @       || (fullness[i] != \old(fullness)[i] 
    @          && emptiness[i] == \old(emptiness)[i]))
    @     && 
    @     (\forall int j; j>=1 && j < MAX + 1; 
    @              i == j ||
    @              ( emptiness[j] == \old(emptiness[j]) 
    @                && fullness[j] == \old(fullness[j]) )
    @         )
    @      )
    @   );
    @*/
  //@ ensures signaled == 0 || signaled == 1;
  private void unblockingCode(){
    signaled = 0;
    for (int i = 1; i <= MAX && signaled == 0; i++){
      if (fullness[i].waiting() > 0) {
        fullness[i].signal();
        //@ assert cpreGet(i);
        signaled++;
      }
    }
    for (int i = 1; i <= MAX && signaled == 0; i++){
      if (emptiness[i].waiting() > 0) {
        emptiness[i].signal();
        //@ assert cprePut(i);
        signaled++;
      }
    }  

  }
}
