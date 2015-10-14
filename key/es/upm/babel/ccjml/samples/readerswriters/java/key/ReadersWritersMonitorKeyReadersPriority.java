package es.upm.babel.ccjml.samples.readerswriters.java.key;

public class ReadersWritersMonitorKeyReadersPriority{
  
  /** INNER STATE */

  /*@ public instance invariant 
    @    readers >= 0 && writers >= 0 &&
    @    (readers > 0 ==> writers == 0) &&
    @    (writers > 0 ==> readers == 0 && writers == 1);
    @*/
  protected /*@ spec_public @*/ int readers;  
  protected /*@ spec_public @*/ int writer;

  /** For every method, we declare its CPRE as a method */
  //@ ensures \result == (activeReaders == 0 && !activeWriter);
  protected /*@ pure @*/ boolean cpreBeforeWrite() {
    return readers == 0 && writer == 0;
  }

  //@ ensures \result == (!activeWriter && writers == 0);
  protected /*@ pure @*/ boolean cpreBeforeRead() {
    return writer == 0 && writerCondWaiting == 0;
  }
  
  /** Concurrent Mechanism instrumentation - MONITORs */
  //@ public invariant writersCondWaiting >= 0;
  protected /*@ spec_public @*/int writerCondWaiting;
  //@ public invariant readersCondWaiting >= 0;
  protected /*@ spec_public @*/int readersCondWaiting;

  // prop_0_1_signal depicted as an invariant
  //@ public invariant signaled >= 0 && signaled <= 1;
  private /*@ spec_public @*/int signaled ;


  //@ requires !activeWriter && activeReaders == 0; // pre implicit from code
  //@ assignable readers, writers , signaled;
  //@ assignable activeReaders, activeWriter;
  // prop_signal_0_1
  /*@ ensures 
    @   ( readers == \old(readers) && writers == \old(writers)) ||
    @   ( readers + 1 == \old(readers) && writers == \old(writers)) ||
    @   ( readers == \old(readers) && writers + 1 == \old(writers)) ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @   signaled == 1
    @   ==>
    @   ( readers + 1 == \old(readers) || writers + 1 == \old(writers) );
    @*/
  // prop_signal_and_return
  /*@ ensures activeReaders == \old(activeReaders) && 
    @         activeWriter == \old(activeWriter);
    @*/
  //prop_safe_signal
  /*@ ensures
    @   ( readers + 1 == \old(readers) ==> cpreBeforeRead()) &&
    @   ( writers + 1 == \old(writers) ==> cpreBeforeWrite()) ;
    @*/
  //prop_liveness
  /*@ ensures 
    @   ( \old(readers) > 0 && cpreBeforeRead() 
    @   || \old(writers) > 0 && cpreBeforeWrite())
    @   ==>
    @   signaled == 1;
    @*/
  public void afterWriteResumeThread() { 
    signaled = 0;
    if (writers > 0){
        writers--;
        signaled++;
    } else if (readers > 0){
        readers--;
        signaled++;
    } 
  }
  
  //@ requires !activeWriter; // pre implicit from code
  //@ requires activeReaders > 0;
  //@ assignable readers, writers , signaled;
  //@ assignable activeReaders, activeWriter;
  //@ ensures writers == \old(writers);
  // prop_signal_0_1
  /*@ ensures 
    @   ( readers == \old(readers) && writers == \old(writers)) ||
    @   ( readers + 1 == \old(readers) && writers == \old(writers)) ||
    @   ( readers == \old(readers) && writers + 1 == \old(writers)) ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @   signaled == 1
    @   ==>
    @   ( readers + 1 == \old(readers) || writers + 1 == \old(writers) );
    @*/
  // prop_signal_and_return
  /*@ ensures activeReaders == \old(activeReaders) && 
    @         activeWriter == \old(activeWriter);
    @*/
  //prop_safe_signal
  /*@ ensures
    @   ( readers + 1 == \old(readers) ==> cpreBeforeRead()) &&
    @   ( writers + 1 == \old(writers) ==> cpreBeforeWrite()) ;
    @*/
  //prop_liveness
  /*@ ensures 
    @   ( \old(readers) > 0 && cpreBeforeRead() 
    @   || \old(writers) > 0 && cpreBeforeWrite())
    @   ==>
    @   signaled == 1;
    @*/
  public void beforeReadResumeThread() {
    signaled = 0;
    if (readers > 0 && writers == 0) {
      readers--; // two or more process can read simultaneously
      signaled++;
    }
  }

  //@ requires !activeWriter; // pre implicit from code
  //@ assignable readers, writers , signaled;
  //@ assignable activeReaders, activeWriter;
  // prop_signal_0_1
  /*@ ensures 
    @   ( readers == \old(readers) && writers == \old(writers)) ||
    @   ( readers + 1 == \old(readers) && writers == \old(writers)) ||
    @   ( readers == \old(readers) && writers + 1 == \old(writers)) ;
    @*/
  // prop_signal_effective
  /*@ ensures
    @   signaled == 1
    @   ==>
    @   ( readers + 1 == \old(readers) || writers + 1 == \old(writers) );
    @*/
  // prop_signal_and_return
  /*@ ensures activeReaders == \old(activeReaders) && 
    @         activeWriter == \old(activeWriter);
    @*/
  //prop_safe_signal
  /*@ ensures
    @   ( readers + 1 == \old(readers) ==> cpreBeforeRead()) &&
    @   ( writers + 1 == \old(writers) ==> cpreBeforeWrite()) ;
    @*/
  //prop_liveness
  /*@ ensures 
    @   ( \old(readers) > 0 && cpreBeforeRead()
    @   || \old(writers) > 0 && cpreBeforeWrite())
    @   ==>
    @   signaled == 1;
    @*/
  public void afterReadResumeThread()  { 
    signaled = 0;
    if (readers == 0 && writers > 0){
      writers--; // to avoid starvation when no readers
      signaled++;
    } else if (readers > 0 && writers == 0){
      readers--; 
      signaled++;
    }
  }
}
