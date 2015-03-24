package es.upm.babel.ccjml.samples.readerswriters.java.key.csp;



public class ReadersWritersCSPDeferredRequestKeYOptimized {
  
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
   *  For Every Channel, we create a int representing the ammount of requests.
   *  The size of the list corresponds with the messages waiting in the channel.
   */  
  /*@ public invariant beforeWriteRequests >=0 && 
    @                  afterWriteRequests >=0 && 
    @                  beforeReadRequests >=0 && 
    @                  afterReadRequests >=0; 
    @*/
  private int beforeWriteRequests;
  private int beforeReadRequests;
  private int afterWriteRequests;
  private int afterReadRequests;
  
  public ReadersWritersCSPDeferredRequestKeYOptimized() {}

  // SERVER SIDE CODE
  
  /** Auxiliary variables to express 'assume' constraints as verifiable by KeY */
  //  explain each of the and why is that generally
  // safety
  private boolean cprePreservation;
  
  /*@ requires beforeWriteRequests +
    @          beforeReadRequests +
    @          afterWriteRequests +
    @          afterReadRequests <= 10;
    @*/
  //@ requires beforeReadRequests > 3;
  //@ requires beforeWriteRequests > 3;
  //@ assignable beforeReadRequests, beforeWriteRequests;
  //@ assignable cprePreservation;
  //@ assignable readers, writers;
  //@ ensures cprePreservation;
  //prop_liveness
  /* ensures (beforeReadRequests > 0 ==> !cpreBeforeRead()) && 
    @         (beforeWriteRequests > 0 ==> !cpreBeforeWrite()) &&
    @         (afterReadRequests > 0 ==> !true) &&
    @         (afterWriteRequests > 0 ==> !true) && 
    @         ;
    @*/
  //prop_liveness using protocols notion
  /*@ ensures (beforeReadRequests > 0 ==> !cpreBeforeRead()) && 
    @         (beforeWriteRequests > 0 ==> !cpreBeforeWrite()) &&
    @         (afterReadRequests > 0 ==> !(readers > 0)) &&
    @         (afterWriteRequests > 0 ==> !(writers > 0)) && 
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
     
       queueSize = beforeReadRequests;
       for(int i = 0; i < queueSize;i++) {
         if (writers == 0){
           cprePreservation &= cpreBeforeRead();
           beforeReadRequests --;
           this.innerBeforeRead(); 
           requestProcessed = true; 
         }  else {
           break;
         }
       }
     
       queueSize = afterWriteRequests;
       for(int i = 0; i < queueSize;i++) {
         if (writers > 0){
           cprePreservation &= true;
           afterWriteRequests --;
           this.innerAfterWrite(); 
           requestProcessed = true; 
         } else {
           break;
         }
       }
     
       queueSize = afterReadRequests;
       for(int i = 0; i < queueSize;i++) {
         if (readers > 0){
           cprePreservation &= true;
           afterReadRequests --;
           this.innerAfterRead(); 
           requestProcessed = true; 
         } else {
           break;
         }
       }
      // System.out.println(requestProcessed + "--- " + toString());  
      // System.out.println("cprePreservation =" +cprePreservation);
     } // end while

    // System.out.println("liveness =" +liveness);
    // System.out.println("cprePreservation =" +cprePreservation);
  } // end run
    

  // public static void main(String[] args)   {
  //   new ReadersWritersCSPDeferredRequestKeYOptimized().processRequest();
  // }
  
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
//            "bR = "+ beforeReadRequests + " | " +
//            "aR = "+ afterReadRequests + " | " +
//            "bW = "+ beforeWriteRequests + " | " +
//            "aW = "+ afterWriteRequests +"]";
//  }
}
