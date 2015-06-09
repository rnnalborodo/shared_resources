package es.upm.babel.ccjml.samples.multibuffer.java;

import java.util.logging.Logger;

import es.upm.babel.cclib.Monitor;

/** 
 * Multibuffer implementation using locks and conditions. 
 *
 * @author BABEL Group
 */
public class MultibufferMonitorOptimized extends AMultibuffer{
  
  private final static Logger log = Logger.getLogger(MultibufferMonitor.class.getName());
  
  /** Guarantee mutual exclusion in critic sections */
  private final Monitor mutex;
  private final Monitor.Cond[] emptiness;
  private final Monitor.Cond[] fullness;
  
  //@ public normal_behaviour
  //@ ensures \result == maxData > 0 && data.length() <= maxData;
  //@ public model pure boolean invariant();
  public MultibufferMonitorOptimized(int m) {
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
    //@assume els.length <= maxData / 2 && invariant();
    mutex.enter();

    if (els.length > MAX - nData) {
//      log.info("Sleep Put -> "+ Thread.currentThread().getId());
      emptiness[els.length].await();
       //@ assume (els.length <= maxData / 2) && invariant() && (els.length <= nSlots());
    }

//    log.info("Awaken Put -> "+ Thread.currentThread().getId());
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
//      log.info("Sleep Get -> "+ Thread.currentThread().getId());
      fullness[n].await();
      //@ assume (n <= maxData / 2) && invariant() &&  n <= nData();
    }
    
//    log.info("Awaken Get -> "+ Thread.currentThread().getId());
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
    for (int i = nData; i > 0 && signaled == 0; i--){
      if (fullness[i].waiting() > 0) {
        fullness[i].signal();
        //@ assert cpreGet(i);
        signaled++;
      }
    }
    for (int i = MAX-nData; i > 0 && signaled == 0; i--){
      if (emptiness[i].waiting() > 0) {
        emptiness[i].signal();
        //@ assert cprePut(i);
        signaled++;
      }
    }  

  }
}
