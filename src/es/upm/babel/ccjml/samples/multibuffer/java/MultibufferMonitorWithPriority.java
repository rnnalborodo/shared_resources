package es.upm.babel.ccjml.samples.multibuffer.java;

import java.util.LinkedList;
import java.util.List;
import java.util.logging.Logger;

import es.upm.babel.ccjml.samples.utils.Tuple;
import es.upm.babel.cclib.Monitor;
import es.upm.babel.cclib.Monitor.Cond;

/** 
 * Multibuffer implementation using locks and conditions. 
 *
 * @author BABEL Group
 */
public class MultibufferMonitorWithPriority extends AMultibuffer {
  
  private final Logger log = Logger.getLogger(MultibufferMonitorWithPriority.class.getName());
  
  /** Guarantee mutual exclusion in critic sections */
  private final Monitor mutex;
  private final List<Tuple<Monitor.Cond , Tuple<Integer, Integer>>> waiting;
  
  private static final int PUT = 1;
  private static final int GET = 0;
  

  
  //@ public normal_behaviour
  //@ ensures \result == maxData > 0 && data.length() <= maxData;
  //@ public model pure boolean invariant();
  public MultibufferMonitorWithPriority(int m) {
    MAX = m;
    this.nData = 0;
    this.buffer = new Object[m];
    this.first = 0;

    // initialization of concurrent elements
    this.mutex = new Monitor();
    this.waiting = new LinkedList<>();
  }
  
  @Override
  public void put(Object[] els) {
    //@assume els.length <= maxData / 2 && invariant();
    mutex.enter();
    
    if (!cprePut(els.length)) {
      Cond cond = mutex.newCond();
      waiting.add(new Tuple(cond, new Tuple(PUT, els.length)));
      cond.await();
       //@ assume (els.length <= maxData / 2) && invariant() && (els.length <= nSlots());
    }

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
    if (!cpreGet(n)){
      Cond cond = mutex.newCond();
      waiting.add(new Tuple(cond, new Tuple(GET, n)));
      cond.await();
      //@ assume (n <= maxData / 2) && invariant() &&  n <= nData();
    }
    
    Object[] gotData = new Object[n];
    for (int i = 0; i < n; i++) {
      gotData[i] = buffer[first];
      buffer[first] = null;
      first++;
      first %= MAX; 
    }
    nData-= n;
    //@ assert \result.length == n && JMLObjectSequence.convertFrom(\result).concat(data) == \old(data) && invariant();
    unblobckingCode();
    
    mutex.leave();
    return gotData;
  }

  private void unblobckingCode(){
    int found = -1;
    for (int i = 0; i < waiting.size(); i++) {
      Tuple<Cond, Tuple<Integer, Integer>> current = waiting.get(i);
      
      boolean foundToResumePUT = current.getSnd().getFst() == PUT && cprePut(current.getSnd().getSnd());
      boolean foundToResumeGET = current.getSnd().getFst() == GET && cpreGet(current.getSnd().getSnd());
      
      if (foundToResumePUT || foundToResumeGET){
        found = i;
        break;
      }
    }  

    if (found != -1 ){
      Tuple<Cond, Tuple<Integer, Integer>> current = waiting.get(found);
      waiting.remove(current);
      current.getFst().signal();
    }
      
  }
}
