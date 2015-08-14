 package es.upm.babel.ccjml.samples.boundedsemaphore.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.Guard;

import es.upm.babel.ccjml.samples.semaphore.java.pRequest;
import es.upm.babel.ccjml.samples.semaphore.java.vRequests;

/**
 * Semaphore implementation using JCSP Library using channel replication.
 *
 * @author BABEL Group
 */
public class BoundedSemaphoreCSP implements BoundedSemaphore, CSProcess {
  
  /** SHARED RESOURCE IMPLEMENTATION */
  //@ public instance invariant value >= 0 && value <= bound;
  private int value;
  //@ public instance invariant 0 < bound;
  private int bound;
  
  /** WRAPPER IMPLEMENTATION */
  /** Channel for receiving external request for each method */
  private final Any2OneChannel ch_v = Channel.any2one();
  private final Any2OneChannel ch_p = Channel.any2one();

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
  
  @Override
  public void v() {
    //@ assume true;
    ch_v.out().write(new vRequests());
  }
  
  @Override
  public void p() {
    //@ assume true;
    ch_p.out().write(new pRequest());
  }
  
  /** SERVER IMPLEMENTATION */
  /** Constants representing the method presented in the API */
  final int V = 0;
  final int P = 1;

  @Override
  public void run() {
    /*
     * One entry for each associated predicated
     */
    Guard[] guards = {
      ch_v.in(),
      ch_p.in()
    };

    final Alternative services = new Alternative(guards);
    int chosenService;

    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean syncCond[] = new boolean[2];
    //@ assume syncCond.length == 2;

    
    while (true) {
      // refreshing synchronization conditions
      syncCond[V] = this.value < this.bound;
      syncCond[P] = this.value > 0;
      //@ assert syncCond[0] ==> cpreV();
      //@ assert syncCond[1] ==> cpreP();
      //@ assert syncCond.length == 2;

      chosenService = services.fairSelect(syncCond);

      switch(chosenService){
        case V: 
          //@ assert cpreV();
          ChannelInput in = ch_v.in();
          in.read();
          innerV();
          break;

        case P:
          //@ assert cpreV();
          ChannelInput input = ch_p.in();
          input.read();
          innerP();
      }
    }
  }

  //@ public normal_behaviour
  //@   cond_sync value > 0;
  //@   ensures value == \old(value) + 1;
  private void innerV() {
    value++;
  }
  
  //@ public normal_behaviour
  //@   cond_sync value > 0;
  //@   ensures value == \old(value) - 1;
  private void innerP(){
    value--;
  }
}
