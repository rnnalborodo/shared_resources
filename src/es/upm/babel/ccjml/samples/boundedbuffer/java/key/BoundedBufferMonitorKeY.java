package es.upm.babel.ccjml.samples.boundedbuffer.java.key;
/**
 * @author rnnalborodo
 */
public class BoundedBufferMonitorKeY {
   
  //@ public invariant MAX == 2;
  protected static final int MAX = 2;

  // Instance members: shared resource internal state
  /*@ public invariant
    @  0 <= nData && nData <= MAX;
    @*/
  private /*@ spec_public @*/ int nData;  
  /*@ public invariant 0 <= first && first < MAX; @*/
  private /*@ spec_public @*/ int first;
  
  /*@ public invariant buffer.length == MAX; @*/
  private /*@spec_public@*/ int[] buffer;
  // ------------------------ concurrency instrumentation ------------------------

  //@ public invariant  getCond >= 0;
  private /*@ spec_public @*/int getCond;

  //@ public invariant  putCond >= 0;
  private /*@ spec_public @*/int putCond;

  // prop_0_1_signal depicted as an invariant
  //@ public invariant signaled >= 0 && signaled <= 1;
  private /*@ spec_public @*/int signaled;
  
  //@ ensures \result == nData < MAX ;
  private boolean cprePut() {
    return nData < MAX;
  }

  //@ ensures \result == nData > 0;
  private boolean cpreGet() {
    return nData > 0;
  }
  
  //@ assignable signaled, getCond, putCond;
  //@ assignable first, buffer, nData;
  //prop_safe_signal
  /*@  ensures 
     @    (\old(putCond) == putCond + 1 ==> cprePut()) ||
     @    (\old(getCond)== getCond+1 ==> cpreGet())
     @  ;
     @*/
  //prop_0_1_signal
  /*@  ensures 
     @    (\old(putCond) == putCond + 1 && \old(getCond)== getCond ) ||
     @    (\old(getCond) == getCond + 1 && \old(putCond)== putCond )  ||
     @    (\old(getCond) == getCond && \old(putCond)== putCond ) 
     @  ;
     @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (
    @    \old(putCond) > 0 && cprePut() ||
    @    \old(getCond) > 0 && cpreGet()
    @  );
    @*/
  // prop_liveness
  /*@ ensures
    @  (
    @    \old(putCond) > 0 && cprePut() ||
    @    \old(getCond) > 0 && cpreGet()
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
    if (nData > 0 && getCond > 0) {
      getCond--;
      signaled++;
    } else if (nData < MAX  && putCond > 0 ) {
      putCond--;
      signaled++;
    }
  }

}
