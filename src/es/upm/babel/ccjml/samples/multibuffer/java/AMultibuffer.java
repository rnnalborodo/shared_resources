package es.upm.babel.ccjml.samples.multibuffer.java;

public abstract class AMultibuffer implements Multibuffer{
  // Class members
  /*@ public invariant
    @   MAX == 4;
    @*/
  protected int MAX;/*@ in maxData; @*/
  /*@ private represents maxData <- MAX; @*/

  // Instance members: shared resource internal state
  /*@ public invariant 0 <= first && first < MAX; @*/
  protected /*@ spec_public @*/ int first; /*@ in data; @*/
  
  /*@ public invariant 0 <= nData && nData <= MAX; @*/
  protected /*@ spec_public @*/ int nData; /*@ in data; @*/
  
  protected /*@spec_public@*/ Object[] buffer;/*@ in data; @*/
  /*@ private represents
    @   data <- nData == 0
    @     ? JMLObjectSequence.EMPTY 
    @     : first + nData <= max   
    @     ? JMLObjectSequence.convertFrom(buffer).subsequence(first, first + nData - 1)
    @     : JMLObjectSequence.convertFrom(buffer).subsequence(first, maxData - 1).
    @     concat(JMLObjectSequence.convertFrom(buffer,(first + nData) % max - 1)); 
    @*/
  
  //@ requires n > 0;
  //@ ensures \result == n > MAX - nData
  protected boolean cprePut(int n){
    return MAX - nData >= n;
  }

  //@ requires n > 0;
  //@ ensures \result == n <= nData
  protected boolean cpreGet(int n) {
    return n <= nData;
  }
  
  public int maxData(){
    return MAX;
  }
  
}
