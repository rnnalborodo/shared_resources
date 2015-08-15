package es.upm.babel.ccjml.samples.bufferoddeven.java;

import java.util.Arrays;

import es.upm.babel.cclib.Monitor;
import es.upm.babel.cclib.Monitor.Cond;

/** 
 * BufferOddEven implementation using monitors and conditions.
 *
 * @author BABEL Group
 */
public class BufferOddEvenMonitor implements BufferOddEven {

  protected final int MAX;
  
  protected int[] buffer; /*@ in data; @*/
  protected int first;/*@ in data; @*/
  protected int nData;/*@ in data; @*/
  /*@ private represents
    @   data <- nData == 0
    @       ? JMLObjectSequence.EMPTY 
    @       : first + nData <= max
    @       ? JMLObjectSequence.convertFrom(buffer).subsequence(first, first + nData - 1)
    @       : JMLObjectSequence.convertFrom(buffer).subsequence(first, maxData - 1).
    @         concat(JMLObjectSequence.convertFrom(buffer,(first + nData) % max - 1)); 
  @*/
  
  protected Monitor mutex;
  protected Cond evenCond;
  protected Cond oddCond;
  protected Cond putCond;
  
  public BufferOddEvenMonitor(){
    this(10);
  }
  
  public BufferOddEvenMonitor(int m){
    MAX = m;
    buffer = new int[MAX];
    first = 0;
    nData = 0;
    
    mutex = new Monitor();
    evenCond = mutex.newCond();
    oddCond = mutex.newCond();
    putCond = mutex.newCond();
  }

  /*@ public normal_behaviour
    @  ensures \result == nData <= MAX - 1;
    @*/
  private boolean cprePut() {
    return nData <= MAX - 1;
  }

  /*@ public normal_behaviour
    @  requires t == EVEN || t == ODD;
    @  ensures \result == (t == ODD && buffer[first] % 2 == 1) || 
    @          (t == EVEN && buffer[first] % 2 == 0)  ;
    @*/
  private boolean cpreGet(Type t) {
    return nData > 0 && ((buffer[first] % 2 == 0 && t == Type.EVEN) || 
                         (buffer[first] % 2 == 1 && t == Type.ODD));
  }

  @Override
  public void put(int d) {
    //@ assume true;
    mutex.enter();
    if (!cprePut()) {
      putCond.await();
    }
    
    //@ assert cprePut();
    buffer[(first + nData) % MAX ] = d;
    nData++;
    
    int signaled = 0;
    
    if (nData > 0 && buffer[first] % 2 == 0 && evenCond.waiting()> 0) {
      evenCond.signal();
      signaled++;
    } else if (nData > 0 && buffer[first] % 2 == 1 && oddCond.waiting()> 0) {
      oddCond.signal();
      signaled++;
    } else if (nData < MAX  && putCond.waiting() > 0 ) {
      putCond.signal();
      signaled++;
    }
    
    //@ assert signaled == 0 || signaled == 1;
    mutex.leave();
  }

  @Override
  public  int get(Type t) {
    //@assume t == EVEN || t == ODD;
    mutex.enter();
    
    if (!cpreGet(t)) {
      if (t.equals(Type.ODD))
        oddCond.await();
      else 
        evenCond.await();
    }
    
    //@ assert cpreGet(t);
    int d = buffer[first];
    buffer[first] = -1;
    first ++;
    first%=MAX;
    nData--;
    
//    int signaled = 0;
    if (nData > 0 && buffer[first] % 2 == 0 && evenCond.waiting()> 0) {
      evenCond.signal();
//      signaled++;
    } else if (nData > 0 && buffer[first] % 2 == 1 && oddCond.waiting()> 0) {
      oddCond.signal();
//      signaled++;
    } else if (nData < MAX  && putCond.waiting() > 0 ) {
      putCond.signal();
//      signaled++;
    }
    
    //@ assert signaled == 0 || signaled == 1;
    mutex.leave();
    return d;
  }

  @Override
  public String toString(){
    return "buffer = " + Arrays.toString(buffer) + " - fst = " + first;
  }
  
}
