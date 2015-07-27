package es.upm.babel.ccjml.samples.multibuffer.java.key;

import es.upm.babel.ccjml.samples.csp.list.src.List;
  
/** 
 * Multibuffer implementation JCSP Library with deferred request processing.
 * KeY Instrumentation 
 *
 * @author BABEL Group
 */
public class MultibufferCSPDeferredRequestKeY {

  /** SHARED RESOURCE IMPLEMENTATION */
  //@ public invariant MAX == 1;
  public static final int MAX = 1;

  // Instance members: shared resource internal state
  /*@ public invariant
    @  0 <= nData && nData <= MAX;
    @*/
  private /*@ spec_public @*/ int nData;  
  /*@ public invariant 0 <= first && first < MAX; @*/
  private /*@ spec_public @*/ int first;
  
  /*@ public invariant buffer.length == MAX; @*/
  private /*@spec_public@*/ int[] buffer;
  
  /** WRAPPER IMPLEMENTATION */      
  /** 
   * List for enqueue all request for each method
   */
  private /*@ spec_public @*/List producerRequests;
  private /*@ spec_public @*/List consumerRequests;

  /** SERVER IMPLEMENTATION */
  /** Constants representing API method's */
  
  private static final int PUT = 0;
  private static final int GET = 1;
  private static final int QUEUE_HEAD = 0;

  /** KeY Instrumentation - Prop variables */
  private boolean cprePreservation;
  private boolean effectiveness;
  
  //@ requires producerRequests.size() + consumerRequests.size() >= 2;
  //@ assignable cprePreservation;
  //@ assignable buffer[*], first, nData;
  //@ ensures cprePreservation;
  //@ ensures effectiveness;
  public void processRequest() {
    cprePreservation = effectiveness = true;
    /**
     * Unblocking code
     * Must always process all request which is associated CPRE holds
     */
    boolean anyResumed;
    do {
      anyResumed = false;

      int lastItem = producerRequests.size();
      for (int i = 0; i < lastItem; i++) {
        int r = (int) producerRequests.get(QUEUE_HEAD);

        if (r <= MAX/2 - nData){
          cprePreservation &= (r <= MAX / 2- nData);
          producerRequests.remove(r);
          
          this.innerPut(getValues(r));
          
          anyResumed = true; 
        } else {
          effectiveness &= !(r <= MAX / 2- nData);
          
        }
      }

      lastItem = consumerRequests.size();
      for (int i = 0; i < lastItem; i++) {
        int n = (int) consumerRequests.get(QUEUE_HEAD);
        
        if (n <= nData){
          cprePreservation &= (n <= nData / 2);
          
          this.innerGet(n);
          consumerRequests.remove(n);
          anyResumed = true;
        } else {
          effectiveness &= !(n <= nData / 2); 
        }
      }
    } while (anyResumed);
  }

  //@ requires els.length <= MAX - buffer.length;
  private void innerPut(int[] els){
    for (int el : els) {
      buffer[(first + nData) % MAX] = el;
      nData++;
    }
  }

  //@ requires n <= buffer.length;
  private Object[] innerGet(int n){
    Object[] result = new Object[n];
    for (int j = 0; j < n; j++) {
      result[j] = buffer[first];
      buffer[first] = -1;
      first++;
      first %= MAX;
    }
    nData -= n;
    return result;
  }
  
  private int[] getValues(int c){
    int[] array = new int[c];
    for (int i = 0; i < c; i++) {
      array[i] = 0; 
    }
    return array;
  }
}
