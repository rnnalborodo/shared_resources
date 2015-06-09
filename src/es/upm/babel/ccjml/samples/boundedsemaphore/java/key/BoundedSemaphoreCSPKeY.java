 package es.upm.babel.ccjml.samples.boundedsemaphore.java.key;

/**
 * Semaphore instrumentation using JCSP Library for KeY verification.
 */
public class BoundedSemaphoreCSPKeY {
  
  //@ public instance invariant value >= 0 && value <= bound;
  private int value;
  //@ public instance invariant 0 < bound;
  private int bound;
  
  //@ public instance invariant vChannel >=0;
  private int vChannel;
  //@ public instance invariant pChannel >=0;
  private int pChannel;

  public BoundedSemaphoreCSP(int v){
    bound = v;
    value = 0;
  }

  //@ensures \result == value < bound;
  private boolean cpreV(){
    return value < bound;
  }
  
  //@ensures \result == value > 0;
  private boolean cpreP(){
    return value > 0;
  }

  //@ requires (syncCond.length == 4 && guards.length == 4);
  //@ requires (\forall int j; 0<=j && j < guards.length; guards[j] != null);
  //@ ensures \result >= 0 && \result < syncCond.length;
  //@ ensures syncCond[\result];
  //@ ensures guards[\result].size() > 0; 
  private int /*@ pure @*/ fairSelect(boolean[] syncCond, List[] guards) {
    int selectedService = 0;
    while (selectedService < syncCond.length && !syncCond[selectedService] && guards[selectedService].length > 0)
      selectedService++;

    if (selectedService == syncCond.length)
      return -1;
    else 
      return selectedService;
  }  

  // CSP server side code
  @Override
  public void run() {
    /*
     * One entry for each associated predicated
     */
    private static final int V = 0;
    private static final int P = 1;

    Guard[] inputs = {
      vChannel.in(),
      pChannel.in()
    };

    boolean syncCond[] = new boolean[2];

    //@ assume syncCond.length == 2;

    final Alternative services = new Alternative(inputs, syncCond);
    int chosenService;
    
    while (true) {
      // refreshing synchronization conditions
      syncCond[0] = this.value < this.bound;
      syncCond[1] = this.value > 0;
      //@ assume syncCond[0] ==> cpreV();
      //@ assume syncCond[1] ==> cpreP();
      //@ assume syncCond.length == 2;

      choice = services.fairSelect();

      switch(choice){
        case V: 
          //@ assert true && cpreV();
          ChannelInput in = vChannel.in();
          in.read();
          innerV();
          break;

        case P:
          //@ assert true && cpreV();
          ChannelInput input = pChannel.in();
          input.read();
          innerP();
      }
    }
  }

  
  public void innerV() {
    value++;
  }

  public void innerP(){
    value--;
  }

}
