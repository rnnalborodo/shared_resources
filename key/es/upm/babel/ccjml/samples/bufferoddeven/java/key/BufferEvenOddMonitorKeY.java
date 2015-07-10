package es.upm.babel.ccjml.samples.bufferoddeven.java.key;
/**
 * @author rnnalborodo
 */
public class BufferEvenOddMonitorKeY{
 
  /** INNER STATE */
  //public enum Type { EVEN, ODD }
  protected static final int EVEN = 1;
  protected static final int ODD = 0;
   
  //@ public invariant MAX == 2;
  protected static final int MAX = 2;

  /*@ public invariant
    @  0 <= nData && nData <= MAX;
    @*/
  private /*@ spec_public @*/ int nData;  
  /*@ public invariant 0 <= first && first < MAX; @*/
  private /*@ spec_public @*/ int first;
  
  /*@ public invariant buffer.length == MAX; @*/
  private /*@spec_public@*/ int[] buffer;
  
  /** For every method, we declare its CPRE as a method */
  //@ ensures \result == nData < MAX ;
  private boolean cprePut() {
    return nData < MAX;
  }

  //@ requires t == EVEN || ODD == t;
  /*@ ensures \result == (nData > 0 && ((buffer[first] % 2 == 0 && t == EVEN) || (buffer[first] % 2 == 1 && t == ODD)));
     @*/
  private boolean cpreGet(int t) {
    return nData > 0 && ((buffer[first] % 2 == 0 && t == EVEN) || (buffer[first] % 2 == 1 && t == ODD));
  }
  
  /** Concurrent Mechanism instrumentation - MONITORs */
  // prop_0_1_signal depicted as an invariant
  //@ public invariant signaled >= 0 && signaled <= 1;
  private /*@ spec_public @*/int signaled; 
  
  //@ public invariant  evenCond >= 0;
  private /*@ spec_public @*/int evenCond;

  //@ public invariant  oddCond >= 0;
  private /*@ spec_public @*/int oddCond;

  //@ public invariant  putCond >= 0;
  private /*@ spec_public @*/int putCond;

  
  //@ assignable signaled, evenCond, oddCond, putCond;
  //@ assignable first, buffer, nData;
  //prop_0_1_signal
  /*@  ensures 
     @    (\old(putCond) == putCond + 1 && \old(evenCond)== evenCond && \old(oddCond)== oddCond) ||
     @    (\old(evenCond) == evenCond + 1 && \old(putCond)== putCond && \old(oddCond)== oddCond) ||
     @    (\old(oddCond) == oddCond + 1 && \old(evenCond)== evenCond && \old(putCond)== putCond)  ||
     @    (\old(oddCond) == oddCond && \old(evenCond)== evenCond && \old(putCond)== putCond) 
     @  ;
     @*/
  //prop_safe_signal
  /*@  ensures 
     @    (\old(putCond) == putCond + 1 ==> cprePut()) ||
     @    (\old(evenCond)== evenCond+1 ==> cpreGet(EVEN)) ||
     @    (\old(oddCond) == oddCond + 1 ==> cpreGet(ODD))
     @  ;
     @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @    \old(putCond) > 0 && cprePut() ||
    @    \old(evenCond) > 0 && cpreGet(EVEN) ||
    @    \old(oddCond) > 0 && cpreGet(ODD)
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  (
    @    \old(putCond) > 0 && cprePut() ||
    @    \old(evenCond) > 0 && cpreGet(EVEN) ||
    @    \old(oddCond) > 0 && cpreGet(ODD)
    @  )
    @  ==>
    @    signaled == 1;
    @*/
  // prop_signal_and_return
  /*@ ensures 
    @  first == \old(first) && nData == \old(nData) &&
    @  buffer == \old(buffer) ;
    @*/
  public void unblobckingCode() {
    signaled =0;
    if (nData > 0 && buffer[first] % 2 == 0 && evenCond> 0) {
      evenCond--;
      signaled++;
    } else if (nData > 0 && buffer[first] % 2 == 1 && oddCond> 0) {
      oddCond--;
      signaled++;
    } else if (nData < MAX  && putCond > 0 ) {
      putCond--;
      signaled++;
    }
  }

}
