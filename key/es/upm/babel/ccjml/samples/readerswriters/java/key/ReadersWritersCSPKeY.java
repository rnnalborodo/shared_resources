package es.upm.babel.ccjml.samples.readerswriters.java.key;

public class ReadersWritersCSPKeY {
  
  //@ requires (syncCond.length == guards.length && guards.length > 0);
  //@ requires (syncCond.length <=2);
  /*@ ensures ((\result >= 0 && \result < syncCond.length) && 
    @          (syncCond[\result] && guards[\result] > 0 ))
    @       || (\result == -1 &&
    @         (\forall int i; i >= 0 && i < syncCond.length; 
    @                           !syncCond[i] || guards[i] == 0));
    @*/
  public static int /*@ pure @*/ fairSelect(boolean[] syncCond, int[] guards){
    /*@ maintaining 0<=i && i < syncCond.length
      @                && 
      @                 (\forall int j; 0 <= j && j<i;
      @                       !syncCond[i] || guards[i] == 0);
      @ assignable \nothing;
      @ decreasing syncCond.length-i;
      @*/
    for(int i = 0 ; i < syncCond.length; i++){
      if (syncCond[i] && guards[i] > 0){
        return i;
      }
    }
    return -1;
  }
  
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
  //@ public invariant ch_beforeWrite >=0;
  private int ch_beforeWrite;
  //@ public invariant ch_beforeRead >=0;
  private int ch_beforeRead;
  //@ public invariant ch_afterWrite >=0;
  private int ch_afterWrite;
  //@ public invariant ch_afterRead >=0;
  private int ch_afterRead;
  
  public ReadersWritersCSPKeY() {}

  // SERVER SIDE CODE
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
  private boolean wellFormedGuards;
  private boolean wellFormedSyncCond;
  private boolean propEffectiveFairSelect;
  private boolean propSafeSelection;
  
  /*@ requires ch_beforeWrite +
    @          ch_beforeRead +
    @          ch_afterWrite +
    @          ch_afterRead > 0;
    @*/
  /*@ requires ch_beforeWrite +
    @          ch_beforeRead +
    @          ch_afterWrite +
    @          ch_afterRead <= 2;
    @*/
  //@ assignable wellFormedGuards, wellFormedSyncCond, propEffectiveFairSelect;
  //@ assignable propSafeSelection;
  //@ ensures wellFormedGuards && wellFormedSyncCond;
  //@ ensures propEffectiveFairSelect;
  //@ ensures propSafeSelection;
  public void serverInstance(){
    /** Init the variables as false like basic case */
    wellFormedGuards = true;
    wellFormedSyncCond = true;
    propSafeSelection = true;
    propEffectiveFairSelect = true;
    
    /** Creating Guards (eligible channels) and its correspondence in syncCond */
    int[] guards = {
        ch_beforeWrite,
        ch_beforeRead,
        ch_afterWrite,
        ch_afterRead
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
   
     chosenService = fairSelect(syncCond, guards);
     propEffectiveFairSelect &= 
                      chosenService < guards.length && chosenService >= 0 &&
                      guards[chosenService] > 0 &&
                      syncCond[chosenService];
                     
     switch(chosenService){
   
       case BEFORE_WRITE:
         propSafeSelection &= cpreBeforeWrite();
         innerBeforeWrite();
         guards[BEFORE_WRITE]--;
         break;
   
       case BEFORE_READ:
         propSafeSelection &= cpreBeforeRead();
         innerBeforeRead();
         guards[BEFORE_READ]--;
         break;
   
       case AFTER_WRITE: 
         propSafeSelection &= true;
         innerAfterWrite();
         guards[AFTER_WRITE]--;
         break;
   
       case AFTER_READ:
         propSafeSelection &= true;
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
