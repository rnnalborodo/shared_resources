package es.upm.babel.ccjml.samples.multibuffer.java;

//@ model import org.jmlspecs.models.JMLObjectSequence;

/**
 * Multibuffer implementation with synchronized methods.
 *
 * @author BABEL Group
 */

public class MultibufferSync implements Multibuffer {
  private Object[] buffer; /*@ in data; @*/
  private int first; /*@ in data; @*/
  private int nData; /*@ in data; @*/
  /*@ private represents
    @   data <- nData == 0
    @       ? JMLObjectSequence.EMPTY 
    @       : first + nData <= max
    @       ? JMLObjectSequence.convertFrom(buffer).subsequence(first, first + nData - 1)
    @       : JMLObjectSequence.convertFrom(buffer).subsequence(first, maxData - 1).
    @         concat(JMLObjectSequence.convertFrom(buffer,(first + nData) % max - 1)); @*/
  private int max; /*@ in maxData; @*/
  /*@ private represents maxData <- max; @*/

  public MultibufferSync(int max) {
    this.max = max;
    this.first = 0;
    this.nData = 0;
    this.buffer = new Object[max];
  }
  
  //@ public normal_behaviour
  //@ ensures \result == maxData > 0 && data.length() <= maxData;
  //@ public model pure boolean invariant();

  public int maxData() {
    return max;
  }

  public synchronized void put(Object[] els) {
    //@ assume (els.length <= maxData / 2) && invariant();
    while (max - nData < els.length) {
      try {
        wait();
      } catch (Exception e) { }
    }
    //@ assert (els.length <= maxData / 2) && invariant() && (els.length <= nSlots());
    for (int i = 0; i < els.length; i++) {
      buffer[(first + nData) % max] = els[i];
      nData++;
    }
    //@ assert data == \old(data).concat(JMLObjectSequence.convertFrom(els)) && invariant();
    notifyAll();
  }

  public synchronized Object[] get(int n) {
    //@ assume (n <= maxData / 2) && invariant();
    while (nData < n) {
      try {
        wait();
      } catch (Exception e) {}
    } 
    //@ assert (n <= maxData / 2) && invariant() &&  n <= nData();
    Object[] gotData = new Object[n];
    for (int i = 0; i < n; i++) {
      gotData[i] = buffer[first];
      buffer[first] = null;
      first++;
      first %= max; 
      nData--;
    }
    //@ assert \result.length == n && JMLObjectSequence.convertFrom(\result).concat(data) == \old(data) && invariant();
    notifyAll();
    return gotData;
  }
}
