package es.upm.babel.ccjml.samples.readerswriters.java.key;

/** 
  * ReadersWriters implementation using Babel Priority Monitors.
  * KeY Instrumentation.
  * 
  * @author Babel Group
  */ 
public class ReadersWritersMonitorKeyReadersPriority{
  
  /** INNER STATE */

  /*@ public instance invariant 
    @    readers >= 0 && writers >= 0 &&
    @    (readers > 0 ==> writers == 0) &&
    @    (writers > 0 ==> readers == 0 && writers == 1);
    @*/
  protected /*@ spec_public @*/ int readers = 0;  
  protected /*@ spec_public @*/ int writers = 0;

  /** For every method, we declare its CPRE as a method */
  //@ public normal_behaviour
  //@   ensures \result == (writers + readers == 0);  
  protected /*@pure@*/ boolean cpreBeforeWrite() {
    return readers == 0 && writers == 0 ;
  }
  //@ public normal_behaviour
  //@   ensures \result == writers == 0;
  protected boolean /*@ pure @*/cpreBeforeRead() {
    return writers == 0;
  }
  
  /** INSTRUMENTATION - MONITORs */
  //@ public invariant writersCondition >= 0;
  protected /*@ spec_public @*/ int writersCondition;
  //@ public invariant readersCondition >= 0;
  protected /*@ spec_public @*/ int readersCondition;

  // prop_0_1_signal depicted as an invariant
  //@ public invariant signaled >= 0 && signaled <= 1;
  private /*@ spec_public @*/ int signaled = 0;

  // Node N0 : n readers and no writer
  // only requires to check readers condition.
  
  //@ requires readers > 0;                    // from code - node (N0)
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
  protected void unblockingCodeN0() {
    signaled = 0;
    // prioritizing readers
    if (readersCondition > 0) {
      readersCondition --;
      signaled ++;
    } 
  }

  // Node 00 : no readers and no writer
  //@ requires readers == 0 && writers == 0;                    // from code - node (N0)
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
  protected void unblockingCode00() {
    signaled = 0;
    // prioritizing readers
    if (readersCondition > 0) {
      readersCondition--;
      signaled ++;
    } else if (writersCondition > 0) { 
      // if no reader can be awaken
      writersCondition--;
      signaled ++;
    }
  }
}
