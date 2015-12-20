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
  //@ public invariant writersCondWaiting >= 0;
  protected /*@ spec_public @*/ int writersCondWaiting;
  //@ public invariant readersCondWaiting >= 0;
  protected /*@ spec_public @*/ int readersCondWaiting;

  // prop_0_1_signal depicted as an invariant
  //@ public invariant signaled >= 0 && signaled <= 1;
  private /*@ spec_public @*/ int signaled = 0;

  // Node N0 : n readers and no writer
  // only requires to check readers condition.
  
  //@ public normal_behaviour
  //@ requires readers > 0;                    // from code - node (N0)
  //@ assignable readersCondWaiting, signaled; // instrumentation
  //@ assignable readers;             // inner state
  // prop_signal_0_1
  /*@ ensures 
    @   readersCondWaiting == \old(readersCondWaiting) ||
    @   readersCondWaiting + 1 == \old(readersCondWaiting);
    @*/
  // prop_signal_effective
  /*@ ensures
    @   signaled == 1 ==>
    @   readersCondWaiting + 1 == \old(readersCondWaiting);
    @*/
  // prop_liveness
  /*@ ensures 
    @   \old(readersCondWaiting) > 0 && cpreBeforeRead() 
    @   ==>
    @   signaled == 1;
    @*/
  //prop_safe_signal
  /*@ ensures
    @   readersCondWaiting + 1 == \old(readersCondWaiting) 
    @   ==> 
    @   cpreBeforeRead();
    @*/
  protected void unblockingCodeN0() {
    signaled = 0;
    // prioritizing readers
    if (readersCondWaiting > 0) {
      readersCondWaiting --;
      signaled ++;
    } 
  }

  // Node 00 : no readers and no writer
  protected void unblockingCode00() {
    signaled = 0;
    // prioritizing readers
    if (readersCondWaiting > 0) {
      readersCondWaiting--;
      signaled ++;
    } else if (writersCondWaiting > 0) { 
      // if no reader can be awaken
      writersCondWaiting--;
      signaled ++;
    }
  }
}
