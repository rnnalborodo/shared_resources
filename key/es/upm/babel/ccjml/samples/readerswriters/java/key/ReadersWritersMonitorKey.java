package es.upm.babel.ccjml.samples.readerswriters.java.key;

/**
 * ReadersWriters implementation using Babel Priority Monitors.
 * KeY Instrumentation.
 * 
 *  Verified 2016 01 05 
 * 
 * @version 1
 * @author Raul Alborodo - Babel Group
 *
 */
public class ReadersWritersMonitorKey{
  
  /** INNER STATE */

  /*@ public invariant readers >= 0 && writers >= 0 &&
    @                     (readers > 0 ==> writers == 0) &&
    @                     (writers > 0 ==> readers == 0 && writers == 1);
    @*/
  protected /*@ spec_public @*/int readers = 0;
  protected /*@ spec_public @*/int writers = 0;
  
  /** For every method, we declare its CPRE as a method */
  //@   ensures \result == (writers + readers == 0);  
  protected /*@pure@*/ boolean cpreBeforeWrite() {
    return readers == 0 && writers == 0 ;
  }

  //@   ensures \result == (writers == 0);
  protected boolean /*@ pure @*/cpreBeforeRead() {
    return writers == 0 && writersCondition == 0;
  }
  
  /** Concurrent Mechanism instrumentation - MONITORs */
  //@ public invariant writersCondition >= 0;
  protected /*@ spec_public @*/int writersCondition;
  //@ public invariant readersCondition >= 0;
  protected /*@ spec_public @*/int readersCondition;

  // prop_0_1_signal depicted as an invariant
  //@ public invariant signaled >= 0 && signaled <= 1;
  private /*@ spec_public @*/int signaled ;

  //@ requires writers == 0 && readers == 0; // pre implicit from code
  //@ assignable readersCondition, writersCondition , signaled;
  //prop_safe_signal
  /*@ ensures
    @   ( (readersCondition + 1 == \old(readersCondition)) ==> cpreBeforeRead()) &&
    @   ( (writersCondition + 1 == \old(writersCondition)) ==> cpreBeforeWrite()) ;
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @   ( readersCondition == \old(readersCondition) && writersCondition == \old(writersCondition)) ||
    @   ( readersCondition + 1 == \old(readersCondition) && writersCondition == \old(writersCondition)) ||
    @   ( readersCondition == \old(readersCondition) && writersCondition + 1 == \old(writersCondition)) ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @   signaled == 1
    @   ==>
    @   ( readersCondition + 1 == \old(readersCondition) || writersCondition + 1 == \old(writersCondition) );
    @*/
  //prop_liveness
  /*@ ensures 
    @   ( \old(readersCondition) > 0 && cpreBeforeRead() 
    @   || \old(writersCondition) > 0 && cpreBeforeWrite())
    @   ==>
    @   signaled == 1;
    @*/
  public void afterWriteResumeThread() { 
    signaled = 0;
    if (writersCondition > 0){
        writersCondition--;
        signaled++;
    } else if (readersCondition > 0){
        readersCondition--;
        signaled++;
    } 
  }
  
  //@ requires writers == 0 && readers > 0; // pre implicit from code
  //@ assignable readersCondition, writersCondition , signaled;
  //prop_safe_signal
  /*@ ensures
    @   ( (readersCondition + 1 == \old(readersCondition)) ==> cpreBeforeRead()) &&
    @   ( (writersCondition + 1 == \old(writersCondition)) ==> cpreBeforeWrite()) ;
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @   ( readersCondition == \old(readersCondition) && writersCondition == \old(writersCondition)) ||
    @   ( readersCondition + 1 == \old(readersCondition) && writersCondition == \old(writersCondition)) ||
    @   ( readersCondition == \old(readersCondition) && writersCondition + 1 == \old(writersCondition)) ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @   signaled == 1
    @   ==>
    @   ( readersCondition + 1 == \old(readersCondition) || writersCondition + 1 == \old(writersCondition) );
    @*/
  //prop_liveness
  /*@ ensures 
    @   ( \old(readersCondition) > 0 && cpreBeforeRead() 
    @   || \old(writersCondition) > 0 && cpreBeforeWrite())
    @   ==>
    @   signaled == 1;
    @*/
  public void beforeReadResumeThread() {
    signaled = 0;
    if (readersCondition > 0 && writersCondition == 0) {
      readersCondition--; // two or more process can read simultaneously
      signaled++;
    }
  }

  //@ requires writers == 0; // pre implicit from code
  //@ assignable readersCondition, writersCondition , signaled;
  //prop_safe_signal
  /*@ ensures
    @   ( (readersCondition + 1 == \old(readersCondition)) ==> cpreBeforeRead()) &&
    @   ( (writersCondition + 1 == \old(writersCondition)) ==> cpreBeforeWrite()) ;
    @*/
  // prop_signal_0_1
  /*@ ensures 
    @   ( readersCondition == \old(readersCondition) && writersCondition == \old(writersCondition)) ||
    @   ( readersCondition + 1 == \old(readersCondition) && writersCondition == \old(writersCondition)) ||
    @   ( readersCondition == \old(readersCondition) && writersCondition + 1 == \old(writersCondition)) ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @   signaled == 1
    @   ==>
    @   ( readersCondition + 1 == \old(readersCondition) || writersCondition + 1 == \old(writersCondition) );
    @*/
  //prop_liveness
  /*@ ensures 
    @   ( \old(readersCondition) > 0 && cpreBeforeRead() 
    @   || \old(writersCondition) > 0 && cpreBeforeWrite())
    @   ==>
    @   signaled == 1;
    @*/
  public void afterReadResumeThread()  { 
    signaled = 0;
    if (readers == 0 && writersCondition > 0){
      writersCondition--; // to avoid starvation when no readers
      signaled++;
    } else if (readersCondition > 0 && writersCondition == 0){
      readersCondition--; 
      signaled++;
    }
  }
}
