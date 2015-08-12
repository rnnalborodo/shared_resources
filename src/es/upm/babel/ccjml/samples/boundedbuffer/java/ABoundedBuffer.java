package es.upm.babel.ccjml.samples.boundedbuffer.java;

/**
 * @author rnnalborodo
 */
public abstract class ABoundedBuffer implements BoundedBuffer {
  
  protected final int MAX; 
  protected int[] buffer; /*@ in data; @*/
  protected int first;/*@ in data; @*/
  protected int nData;/*@ in data; @*/
  /*@ private represents
    @   data <- nData == 0
    @       ? JMLObjectSequence.EMPTY 
    @       : first + nData <= MAX
    @       ? JMLObjectSequence.convertFrom(buffer).subsequence(first, first + nData - 1)
    @       : JMLObjectSequence.convertFrom(buffer).subsequence(first, maxData - 1).
    @         concat(JMLObjectSequence.convertFrom(buffer,(first + nData) % MAX - 1)); 
  @*/
  
  public ABoundedBuffer(int m){
    MAX = m;
    buffer = new int[MAX];
    first = 0;
    nData = 0;
  }
  /**
   * @return  nData <= MAX - 1
   */
  boolean cprePut() {
    return nData <= MAX - 1;
  }

  /**
   * @return  buffer.length <= MAX - 1
   */
  boolean cpreGet() {
    return nData > 0;
  }

  @Override
  public abstract void put(int n);

  @Override
  public abstract int get();
}
