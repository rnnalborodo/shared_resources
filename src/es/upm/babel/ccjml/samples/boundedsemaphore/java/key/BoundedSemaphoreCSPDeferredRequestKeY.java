 package es.upm.babel.ccjml.samples.boundedsemaphore.java.key;

/**
 * Semaphore implementation JCSP Library with deferred request processing. 
 * KeY Instrumentation
 *  
 * @author BABEL Group
 */
public class BoundedSemaphoreCSPDeferredRequestKeY {
  
  /** SHARED RESOURCE IMPLEMENTATION */
  //@ public instance invariant value >= 0 && value <= bound;
  //@ public instance invariant 0 < bound;

  //@ public initially value == 0;
  
  private int value;
  private int bound;
  
  /** WRAPPER IMPLEMENTATION */
  //@ensures \result == value < bound;
  private boolean cpreV(){
    return value < bound;
  }
  
  //@ensures \result == value > 0;
  private boolean cpreP(){
    return value > 0;
  }
  
  /** Channel for receiving external request for each method */
  //@ public invariant vRequests >=0;
  private int vRequests;
  //@ public invariant pRequests >=0;
  private int pRequests;

  public BoundedSemaphoreCSPDeferredRequestKeY(int v){
    bound = v;
    value = 0;
  }

  /** SERVER IMPLEMENTATION */
  /** Constants representing API method's */
  final int V = 0;
  final int P = 1;
  final int QUEUE_HEAD = 0;
  
  private boolean cprePreservation;
  
  /*@ requires vRequests +
    @          pRequests <= 10;
    @*/
  //@ assignable vRequests, pRequests;
  //@ assignable cprePreservation;
  //@ assignable value;
  //@ ensures cprePreservation;
  //prop_effectiveness
  /*@ ensures (pRequests > 0 ==> !cpreP()) && 
    @         (vRequests > 0 ==> !cpreV()) 
    @         ;
    @*/
  public void processRequest(){      
    boolean requestProcessed = true;
    cprePreservation = true;
    while (requestProcessed) {
      requestProcessed = false;

      int lastItem = vRequests;
      for (int i = 0; i < lastItem; i++) {
        if (value < bound) {
          // @ assume cpreV() && invariant() && true;
          cprePreservation &= cpreV();
          this.innerV();
          vRequests--;
          requestProcessed = true;
        } else {
          break; // KeY optimization
          // vRequests.add(vRequests.size(), currentV);
        }
      }

      lastItem = pRequests;
      for (int i = 0; i < lastItem; i++) {
        if (value > 0) {
          // @ assume cpreP() && invariant() && true;
          cprePreservation &= cpreP();
          this.innerP();
          pRequests--;
          requestProcessed = true;
        } else {
          break; // KeY optimization
          // vRequests.add(vRequests.size(), currentV);
        }
      }
    }
  }

  //@ requires value < bound;
  //@ assignable value;
  //@ ensures value == \old(value) + 1;
  private void innerV() {
    value++;
  }

  //@ requires value > 0;
  //@ assignable value;
  //@ ensures value == \old(value) - 1;
  private void innerP(){
    value--;
  }
}
