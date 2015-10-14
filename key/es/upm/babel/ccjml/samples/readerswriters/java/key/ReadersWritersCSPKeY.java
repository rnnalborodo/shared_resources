package es.upm.babel.ccjml.samples.readerswriters.java.key;

import es.upm.babel.ccjml.samples.csp.JCSPKeY;

public class ReadersWritersCSPKeY {
  
  // SR invariant
  /*@ public invariant 
    @      (readers >= 0 && writers >= 0) &&
    @      (readers > 0 ==> writers == 0) &&
    @      (writers > 0 ==> readers == 0) &&
    @      (writers == 0 || writers == 1);
    @*/
  //@ public initially readers == 0 && writers == 0;
  
  protected int readers = 0;
  protected int writers = 0;

  /*@ ensures  \result ==     
    @      (readers >= 0 && writers >= 0) &&
    @      (readers > 0 ==> writers == 0) &&
    @      (writers > 0 ==> readers == 0) &&
    @      (writers == 0 || writers == 1);
    @*/     
  public boolean repOk(){
    return readers >= 0 && writers >= 0 &&
           ((writers == 0 && readers == 0) ||
           (readers > 0 && writers == 0) ||
           (writers > 0 && readers == 0 && writers == 1));
  }

  /** For every method, we declare its CPRE as a method */
  //@ public normal_behaviour
  //@   ensures \result == (writers + readers == 0);  
  protected boolean /*@ pure @*/ cpreBeforeWrite() {
    return readers == 0 && writers == 0 ;
  }

  //@ public normal_behaviour
  //@   ensures \result == writers == 0;
  protected boolean /*@ pure @*/ cpreBeforeRead() {
    return writers == 0;
  }
  
  /** WRAPPER IMPLEMENTATION */
  /**
   *  For Every Channel, we create a list of elements representing the messages.
   *  The size of the list corresponds with the messages waiting in the channel.
   *  In this case, due to the operation CPRE do not depend on parameters, int 
   *  is enough.s 
   */  
  //@ public invariant chBeforeWrite >=0;
  private int chBeforeWrite;
  //@ public invariant chBeforeRead >=0;
  private int chBeforeRead;
  //@ public invariant chAfterWrite >=0;
  private int chAfterWrite;
  //@ public invariant chAfterRead >=0;
  private int chAfterRead;
  
  public ReadersWritersCSPKeY() {}

  /** SERVER IMPLEMENTATION */
  /**
   * Constants representing the method presented in the API
   */
  private static final int BEFORE_WRITE = 0;
  private static final int BEFORE_READ = 1;
  private static final int AFTER_WRITE = 2;
  private static final int AFTER_READ = 3;
    
  /** Auxiliary variables to express 'assume' constraints as verifiable by KeY */
  //  explain each of the and why is that generally
  // safety
  private boolean wellFormedSyncCond;
  private boolean cprePreservation;
  
  /*@ requires chBeforeWrite +
    @          chBeforeRead +
    @          chAfterWrite +
    @          chAfterRead > 0;
    @*/
  //@ assignable wellFormedSyncCond;
  //@ assignable cprePreservation;
  //@ assignable writers, readers;
  //@ ensures wellFormedSyncCond;
  //@ ensures cprePreservation;
  public void serverInstance(){
    /** Init the variables as false like basic case */
    wellFormedSyncCond = true;
    cprePreservation = true;
    
    /** Creating Guards (eligible channels) and its correspondence in syncCond */
    int[] guards = {
        chBeforeWrite,
        chBeforeRead,
        chAfterWrite,
        chAfterRead
      };
    boolean[] syncCond = {
        cpreBeforeWrite(),
        cpreBeforeRead(),
        true,
        true
      };
   
    int chosenService = 0;
    while (chosenService != -1 ) {
      // initially we have not treat any request
      // processedRequest = false;
      // refreshing synchronization condition array
      // possible point to introduce an error
      syncCond[BEFORE_WRITE] = (readers + writers == 0);
      syncCond[BEFORE_READ] = writers == 0;
      syncCond[AFTER_WRITE] = true;
      syncCond[AFTER_READ] = true;
         
      wellFormedSyncCond &= (!syncCond[BEFORE_WRITE] || cpreBeforeWrite()) && 
                            (!syncCond[BEFORE_READ] || cpreBeforeRead()) && 
                            (!syncCond[AFTER_WRITE] || true) && 
                            (!syncCond[AFTER_READ] || true) && 
                            syncCond.length == 4;
   
     chosenService = JCSPKeY.fairSelect(syncCond, guards);
                     
     switch(chosenService){
   
       case BEFORE_WRITE:
         cprePreservation &= cpreBeforeWrite();
         innerBeforeWrite();
         guards[BEFORE_WRITE]--;
         break;
   
       case BEFORE_READ:
         cprePreservation &= cpreBeforeRead();
         innerBeforeRead();
         guards[BEFORE_READ]--;
         break;
   
       case AFTER_WRITE: 
         cprePreservation &= true;
         innerAfterWrite();
         guards[AFTER_WRITE]--;
         break;
   
       case AFTER_READ:
         cprePreservation &= true;
         innerAfterRead();
         guards[AFTER_READ]--;
         break;
     } // end case
    } // end while - fairSelect loop
  } // end service instance 
    
  //@ requires true && cpreBeforeRead();
  //@ assignable readers ;
  //@ ensures readers == \old(readers) + 1;
  protected void innerBeforeRead(){
    readers++;
  }
  
  //@ requires readers > 0 && true;
  //@ assignable readers ;
  //@ ensures readers == \old(readers) - 1;
  protected void innerAfterRead(){
    readers--;
  }
  
  //@ requires true && cpreBeforeWrite();
  //@ assignable writers ;
  //@ ensures writers == \old(writers) + 1;
  protected void innerBeforeWrite(){
    writers++;
  }
  
  //@ requires writers > 0 && true;
  //@ assignable writers;
  //@ ensures writers == \old(writers) - 1;
  protected void innerAfterWrite(){
    writers--;
  }
  
}
