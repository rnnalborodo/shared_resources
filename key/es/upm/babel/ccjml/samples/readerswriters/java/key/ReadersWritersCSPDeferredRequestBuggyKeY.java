package es.upm.babel.ccjml.samples.readerswriters.java.key;

/**
 * Instrumentation following the template. 
 * 
 * condition for processing request of 'after_' are incorrect
 * due to the fact that we need to put PRE formulae as well
 * 
 * @author BABEL Group
 *
 */
public class ReadersWritersCSPDeferredRequestBuggyKeY {
  
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
    @      (writers > 0 ==> (readers == 0 && writers == 1));
    @*/

  //@ public initially readers == 0 && writers == 0;

  /*@ ensures  \result == 
    @      (readers >= 0 && writers >= 0) &&
    @      (readers > 0 ==> writers == 0) &&
    @      (writers > 0 ==> (readers == 0 && writers == 1));
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
   *  For Every Channel, we create a int representing the amount of requests.
   *  The size of the list corresponds with the messages waiting in the channel.
   */  
  /*@ public invariant beforeWriteRequests >=0 && 
    @                  ch_afterWrite >=0 && 
    @                  ch_beforeRead >=0 && 
    @                  ch_afterRead >=0; 
    @*/
  private int beforeWriteRequests;
  private int ch_beforeRead;
  private int ch_afterWrite;
  private int ch_afterRead;

  // SERVER SIDE CODE
  
  /** Auxiliary variables to express 'assume' constraints as verifiable by KeY */
  private boolean cprePreservation;
  
  /*@ requires beforeWriteRequests +
    @          ch_beforeRead +
    @          ch_afterWrite +
    @          ch_afterRead <= 2;
    @*/
  //@ assignable ch_beforeRead, beforeWriteRequests;
  //@ assignable ch_afterRead, ch_afterWrite;
  //@ assignable cprePreservation;
  //@ assignable readers, writers;
  //@ ensures cprePreservation;
  //prop_effectiveness
  /* ensures (ch_beforeRead > 0 ==> !cpreBeforeRead()) && 
    @         (beforeWriteRequests > 0 ==> !cpreBeforeWrite()) &&
    @         (ch_afterRead > 0 ==> !true) &&
    @         (ch_afterWrite > 0 ==> !true)
    @         ;
    @*/
  //prop_effectiveness using protocols notion
  /*@ ensures (ch_beforeRead > 0 ==> !cpreBeforeRead()) && 
    @         (beforeWriteRequests > 0 ==> !cpreBeforeWrite()) &&
    @         (ch_afterRead > 0 ==> !(readers > 0)) &&
    @         (ch_afterWrite > 0 ==> !(writers > 0))
    @         ;
    @*/
  public void processRequest(){
    boolean requestProcessed = true;
    cprePreservation = true;
    int queueSize;
    
    while (requestProcessed) {
      requestProcessed = false;
    
      queueSize = beforeWriteRequests;
      for(int i = 0; i < queueSize;i++) {
        if (writers + readers == 0){
          cprePreservation &=cpreBeforeWrite();
          beforeWriteRequests --;
          this.innerBeforeWrite(); 
          requestProcessed = true;  
        } else { 
          break;
        }
      }
    
      queueSize = ch_beforeRead;
      for(int i = 0; i < queueSize;i++) {
        if (writers == 0){
          cprePreservation &= cpreBeforeRead();
          ch_beforeRead --;
          this.innerBeforeRead(); 
          requestProcessed = true; 
        }  else {
          break;
        }
      }
    
      queueSize = ch_afterWrite;
      for(int i = 0; i < queueSize;i++) {
        if (true){
          cprePreservation &= true;
          ch_afterWrite --;
          this.innerAfterWrite(); 
          requestProcessed = true; 
        } else {
          break;
        }
      }
    
      queueSize = ch_afterRead;
      for(int i = 0; i < queueSize;i++) {
        if (true){
          cprePreservation &= true;
          ch_afterRead --;
          this.innerAfterRead(); 
          requestProcessed = true; 
        } else {
          break;
        }
      }
    } // end while
  } // end run
    
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
  
//  @Override
//  public String toString(){
//    return "RW = [ reader = " + readers + " | writers= " + writers + "]"+ 
//        " - ["+
//            "bR = "+ ch_beforeRead + " | " +
//            "aR = "+ ch_afterRead + " | " +
//            "bW = "+ beforeWriteRequests + " | " +
//            "aW = "+ ch_afterWrite +"]";
//  }
}
