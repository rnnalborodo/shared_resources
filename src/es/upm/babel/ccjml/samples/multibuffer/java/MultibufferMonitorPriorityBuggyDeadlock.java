package es.upm.babel.ccjml.samples.multibuffer.java;

import java.util.ArrayList;
import java.util.List;

import es.upm.babel.cclib.Monitor;

/**
 * Multibuffer implementation using locks and conditions. 
 *
 * @author BABEL Group
 */
public class MultibufferMonitorPriorityBuggyDeadlock extends AMultibuffer {
  
  /** Guarantee mutual exclusion in critic sections */
  private final Monitor mutex;
  private final Monitor.Cond awaitingPut;
  private final List<Integer> awaitingParametersPut;
  
  private final Monitor.Cond awaitingGet;
  private final List<Integer> awaitingParametersGet;
  
  //@ public normal_behaviour
  //@ ensures \result == maxData > 0 && data.length() <= maxData;
  //@ public model pure boolean invariant();
  public MultibufferMonitorPriorityBuggyDeadlock(int m) {
    MAX = m;
    this.nData = 0;
    this.buffer = new Object[m];
    this.first = 0;

    // initialization of concurrent elements
    this.mutex = new Monitor();
    this.awaitingPut = mutex.newCond();
    this.awaitingParametersPut = new ArrayList<>();

    this.awaitingGet = mutex.newCond();
    this.awaitingParametersGet = new ArrayList<>();
  }
  
  @Override
  public void put(Object[] els) {
    //@assume els.length <= maxData / 2 && invariant();
    mutex.enter();

    if (els.length > MAX - nData) {
      awaitingParametersPut.add(awaitingParametersPut.size(), els.length);
      awaitingPut.await();
    }
    
    //@ assert (els.length <= maxData / 2) && invariant() && (els.length <= nSlots());
    int next = first + nData;
    for (Object el : els) {
      buffer[(first + nData) % MAX] = el;
      nData++;
    }
    //@ assert data == \old(data).concat(JMLObjectSequence.convertFrom(els)) && invariant();
    unblobckingCode();
    mutex.leave();
  }

  @Override
  public Object[] get(int n) {
    mutex.enter();
    //@ assume (n <= maxData / 2) && invariant();
    if (nData < n){
      awaitingParametersGet.add(awaitingParametersPut.size(), n);
      awaitingGet.await();
    }
    
    //@ assert (n <= maxData / 2) && invariant() &&  n <= nData();
    Object[] gotData = new Object[n];
    for (int i = 0; i < n; i++) {
      gotData[i] = buffer[first];
      buffer[first] = null;
      first++;
      first %= MAX; 
      nData--;
    }
    
    //@ assert \result.length == n && JMLObjectSequence.convertFrom(\result).concat(data) == \old(data) && invariant();
    unblobckingCode();
    mutex.leave();
    return gotData;
  }

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
  private void unblobckingCode(){
    int signaled = 0;
    if (awaitingPut.waiting() > 0 && cprePut(awaitingParametersPut.get(0))){
      awaitingParametersPut.remove(0);
      awaitingPut.signal();
    } else if (awaitingGet.waiting() > 0 && cpreGet(awaitingParametersGet.get(0))){
      awaitingParametersGet.remove(0);
      awaitingGet.signal();
    } 
  }
}
