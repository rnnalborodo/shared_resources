package es.upm.babel.ccjml.samples.readerswriters.java.key.csp;

import es.upm.babel.ccjml.samples.readerswriters.java.key.csp.list_seq.src.List;


public class ReadersWritersCSPKeY {
  
  protected int readers = 0;
  protected int writers = 0;
  
  /** For every method, we declare its cpre as a method */
  //@ public normal_behaviour
  //@   ensures \result == (writers + readers == 0);  
  protected boolean /*@ pure @*/ cpreBeforeWrite() {
    return readers == 0 && writers == 0 ;
  }

  //@ public normal_behaviour
  //@   ensures \result == writers == 0;
  protected boolean /*@ pure @*/ cpreBeforeRead() {
    return writers ==0;
  }

  // SR invariant
  /*@ public invariant 
    @      (readers >= 0 && writers >= 0) &&
    @      (readers > 0 ==> writers == 0) &&
    @      (writers > 0 ==> readers == 0) &&
    @      (writers == 0 || writers == 1);
    @*/

  //@ public initially readers == 0 && writers == 0;

  /*@ ensures  \result == 
    @      (readers >= 0 && writers >= 0) &&
    @      (readers > 0 ==> writers == 0) &&
    @      (writers > 0 ==> readers == 0) &&
    @      (writers == 0 || writers == 1)     ;
    @*/     
  public boolean /*@ strictly_pure @*/ repOk(){
    return  (readers >= 0 && writers >= 0) &&
            (writers == 0 || writers <= 1) &&
            (
              (readers > 0 && writers == 0) ||
              (writers > 0 && readers == 0) ||
              (readers == 0 && writers == 0)
            );
  }

  /**
   *  For Every Channel, we create a list of elements representing the messages.
   *  The size of the list corresponds with the messages waiting in the channel.
   */  
  private List beforeWriteChannel;
  private List beforeReadChannel;
  private List afterWriteChannel;
  private List afterReadChannel;
  
  public ReadersWritersCSPKeY() {}

  // SERVER SIDE CODE
  /**
   * Constants representing the method presented in the API
   */
  private static final int BEFORE_WRITE = 0;
  private static final int BEFORE_READ = 1;
  private static final int AFTER_WRITE = 2;
  private static final int AFTER_READ = 3;

  //@ requires (syncCond.length == 4 && guards.length == 4);
  //@ requires (\forall int j; 0<=j && j < guards.length; guards[j] != null);
  //@ ensures \result >= 0 && \result < syncCond.length;
  //@ ensures syncCond[\result];
  //@ ensures guards[\result].size() > 0; 
  private int /*@ pure @*/ fairSelect(boolean[] syncCond, List[] guards) {
    int selectedService = 3;
    return selectedService;
  }  
  
  /** Auxiliary variables to express 'assume' constraints as verifiables by KeY */
  //  explain each of the and why is that generally
  // safety
  private boolean wellFormedGuards;
  private boolean wellFormedSyncCond;
  private boolean propEffectiveFairSelect;
  private boolean propSafeSelection;
  
  /*@ requires beforeWriteChannel.size() +
    @          beforeReadChannel.size() +
    @          afterWriteChannel.size() +
    @          afterReadChannel.size() > 0;
    @*/
  /*@ requires beforeWriteChannel.size() +
    @          beforeReadChannel.size() +
    @          afterWriteChannel.size() +
    @          afterReadChannel.size() <= 2;
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
    List[] guards =  {
        beforeWriteChannel,
        beforeReadChannel,
        afterWriteChannel,
        afterReadChannel
      };
    boolean[] syncCond =  {
        cpreBeforeWrite(),
        cpreBeforeRead(),
        true,
        true
      };
   
   // updating variables to be checked
   wellFormedSyncCond = (!syncCond[0] || cpreBeforeWrite()) && 
       (!syncCond[1] || cpreBeforeRead()) && 
       (!syncCond[2] || true) && 
       (!syncCond[3] || true) && syncCond.length == 4;
   wellFormedGuards = guards.length == 4;
   
    boolean processedRequest = true;
    Object token;
    /* loop_invariant beforeWriteChannel +
      @            beforeReadChannel +
      @            afterWriteChannel +
      @            afterReadChannel > 0 &&
      @            wellFormedGuards && wellFormedSyncCond && 
      @            propEffectiveFairSelect && propSafeSelection;
      @ assignable wellFormedGuards, wellFormedSyncCond, 
      @            propEffectiveFairSelect,propSafeSelection;
      @ decreases (beforeWriteChannel +
      @            beforeReadChannel +
      @            afterWriteChannel +
      @            afterReadChannel > 0);
      @*/
    while (beforeWriteChannel.size() +
           beforeReadChannel.size() +
           afterWriteChannel.size() +
           afterReadChannel.size() > 0 
           && !processedRequest
          ) {
      // initially we have not treat any request
      // processedRequest = false;

      // refreshing synchronization condition array
      // possible point to introduce an error
      syncCond[0] = (readers + writers == 0);
      syncCond[1] = writers == 0;
         
      wellFormedSyncCond &= (!syncCond[0] || cpreBeforeWrite()) && 
                            (!syncCond[1] || cpreBeforeRead()) && 
                            (!syncCond[2] || true) && 
                            (!syncCond[3] || true) && 
                            syncCond.length == 4;
   
     int chosenService = fairSelect(syncCond, guards);
     propEffectiveFairSelect &= 
                     chosenService < guards.length && chosenService >= 0 &&
                     guards[chosenService].size() > 0 &&
                     syncCond[chosenService];
                     
     switch(chosenService){
   
       case BEFORE_WRITE:
         propSafeSelection &= cpreBeforeWrite();
         token = beforeWriteChannel.get(0);
         beforeWriteChannel.remove(token);
         innerBeforeWrite();
         break;
   
       case BEFORE_READ:
         propSafeSelection &= cpreBeforeRead();
         token = beforeReadChannel.get(0);
         beforeReadChannel.remove(token);
         innerBeforeRead();
         break;
   
       case AFTER_WRITE: 
         propSafeSelection &= true;
         token = afterWriteChannel.get(0);
         afterWriteChannel.remove(token);
         innerAfterWrite();
         break;
   
       case AFTER_READ:
         propSafeSelection &= true;
         token = afterReadChannel.get(0);
         afterReadChannel.remove(token);
         innerAfterRead();
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
  
  //@ requires readers > 0;
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
  
  //@ requires writers > 0;
  //@ assignable writers;
  //@ ensures writers == \old(writers) - 1;
  protected void innerAfterWrite(){
    writers--;
  }
  
}
