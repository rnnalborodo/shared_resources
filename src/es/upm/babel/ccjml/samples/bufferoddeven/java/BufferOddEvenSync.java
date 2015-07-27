package es.upm.babel.ccjml.samples.bufferoddeven.java;

//@ model import org.jmlspecs.models.JMLObjectSequence;

import java.util.Arrays;

/**
 * BufferOddEven implementation using synchronized methods.
 *
 * @author BABEL Group
 */

public class BufferOddEvenSync implements BufferOddEven {

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
  
  public BufferOddEvenSync(){
    this(10);
  }
  
  public BufferOddEvenSync(int m){
    MAX = m;
    buffer = new int[MAX];
    first = 0;
    nData = 0;
  }

  /*@ public normal_behaviour
    @  ensures \result == nData <= MAX - 1;
    @*/
  private boolean cprePut() {
    return nData <= MAX - 1;
  }

  /*@ public normal_behaviour
    @  requires t == EVEN || t == ODD;
    @  ensures (t == ODD && \result == buffer[first] % 2 == 1) || 
    @          (t == EVEN && \result == buffer[first] % 2 == 0)  ;
    @*/
  private boolean cpreGet(Type t) {
    return nData > 0 && ((buffer[first] % 2 == 0 && t == Type.EVEN) || (buffer[first] % 2 == 1 && t == Type.ODD));
  }
  
  @Override
  public synchronized void put(int d) {
    //@ assume true;
    while (!cprePut()) {
      try {
        wait();
      } catch (InterruptedException ex) { }
    }
    //@ assume nData <= MAX - 1;
    buffer[(first + nData) % MAX ] = d;
    nData++;
    notifyAll();
  }

  @Override
  public synchronized int get(Type t) {
    //@ assume t == EVEN || t == ODD;
    while (!cpreGet(t)) {
      try {
        wait();
      } catch (InterruptedException ex) { }
    }
    //@ assume cpreGet(t);
    int d = buffer[first];
    buffer[first] = -1;
    first++;
    first %= MAX; 
    nData--;
    notifyAll();
    return d;
  }

  @Override
  public String toString(){
    return "buffer = " + Arrays.toString(buffer);
  }
  
}
