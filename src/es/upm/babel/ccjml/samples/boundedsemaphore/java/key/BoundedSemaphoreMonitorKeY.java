package es.upm.babel.ccjml.samples.boundedsemaphore.java.key;

/**
 * @author rnnalborodo
 */
public class BoundedSemaphoreMonitorKeY {

    //@ public invariant v >= 0;
  private /*@ spec_public @*/ int v = 0;
  
  //@ public invariant p >= 0;
  private /*@ spec_public @*/ int p = 0;
  
  //@ public invariant value >=0 && value <= bound;
  private int value;
 
  //@ public invariant bound > 0;
  private int bound ;

  //@ensures \result == value > 0;
  private boolean cpreP(){
    return value > 0;
  }
  
  //@ensures \result == value < bound;
  private boolean cpreV(){
    return value < bound;
  }
  
  // prop_0_1_signal depicted as an invariant
  /*@ public invariant
    @            signaled >= 0 && signaled <= 1;
    @*/
  private /*@ spec_public @*/int signaled  = 0;
  
  //@ assignable signaled, v, p;
  //@ assignable value;
  //prop_safe_signal
  /*@ ensures
     @   (v + 1 == \old(v) ==> cpreV()) && 
     @   (p + 1 == \old(p) ==> cpreP());
     @*/
  // prop_signal_0_1
  /*@ ensures 
     @  (v == \old(v) && p == \old(p)) ||
     @  (v == \old(v) && p +1  == \old(p) ) ||
     @  (v + 1 == \old(v) && p == \old(p));
     @*/
  // prop_signal_effective
  /*@ ensures
    @  signaled == 1
    @  ==>
    @  (v + 1 == \old(v) || p + 1 == \old(p));
    @*/
  // prop_liveness
  /*@ ensures
     @  ( (v > 0 && cpreV()) || (p > 0 && cpreP()))
     @  ==>
     @    signaled == 1;
     @*/
  // prop_signal_and_return
  //@ ensures value == \old(value);
  private void unblobckingCode(){
    signaled =0;
    if (value < bound && v > 0) {
      v--;
      signaled++;
    } else if (value > 0 && p > 0) {
      p--;
      signaled++;
    }
  }
}
