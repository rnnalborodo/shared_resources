 package es.upm.babel.ccjml.samples.boundedsemaphore.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.Guard;

import es.upm.babel.ccjml.samples.semaphore.java.pRequest;
import es.upm.babel.ccjml.samples.semaphore.java.vRequest;

/**
 * Semaphore implementation using JCSP Library with channel expansion.
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
  private final Any2OneChannel vChannel = Channel.any2one();
  private final Any2OneChannel pChannel = Channel.any2one();

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
    vChannel.out().write(new vRequest());
  }
  
  @Override
  public void p() {
    //@ assume true;
    pChannel.out().write(new pRequest());
  }
  
  /** Constants representing API method's */
  final int V = 0;
  final int P = 1;

  /** SERVER IMPLEMENTATION */
  @Override
  public void run() {
    /*
     * One entry for each associated predicated
     */
    Guard[] inputs = {
      vChannel.in(),
      pChannel.in()
    };

    final Alternative services = new Alternative(inputs);
    int choice;

    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean syncCond[] = new boolean[2];
    //@ assume syncCond.length == 2;

    
    while (true) {
      // refreshing synchronization conditions
      syncCond[0] = this.value < this.bound;
      syncCond[1] = this.value > 0;
      //@ assume syncCond[0] ==> cpreV();
      //@ assume syncCond[1] ==> cpreP();
      //@ assume syncCond.length == 2;

      choice = services.fairSelect(syncCond);

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

  private void innerV() {
    value++;
  }

  private void innerP(){
    value--;
  }
}
