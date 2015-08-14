 package es.upm.babel.ccjml.samples.boundedsemaphore.java;

import java.util.ArrayList;
import java.util.List;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;

/**
 * Semaphore implementation JCSP Library with deferred request processing. 
 *
 * @author BABEL Group
 */
public class BoundedSemaphoreCSPDeferredRequest implements BoundedSemaphore, CSProcess {
  
  /** SHARED RESOURCE IMPLEMENTATION */
  //@ public instance invariant value >= 0 && value <= bound;
  private int value;
  //@ public instance invariant 0 < bound;
  private int bound;
  
  /** WRAPPER IMPLEMENTATION */
  private final Any2OneChannel vChannel = Channel.any2one();
  private final Any2OneChannel pChannel = Channel.any2one();
  
  /** 
   * List for enqueue all request for each method
   */
  private final List<One2OneChannel> vRequest = new ArrayList<One2OneChannel>();
  private final List<One2OneChannel> pRequest = new ArrayList<One2OneChannel>();


  public BoundedSemaphoreCSPDeferredRequest(int v){
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
    One2OneChannel innerChannel = Channel.one2one();
    vChannel.out().write(innerChannel);
    innerChannel.in().read();
  }
  
  @Override
  public void p() {
    //@ assume true;
    One2OneChannel innerChannel = Channel.one2one();
    pChannel.out().write(innerChannel);
    innerChannel.in().read();
  }
  
  /** SERVER IMPLEMENTATION */
  /** Constants representing API method's */
  final int V = 0;
  final int P = 1;
  final int QUEUE_HEAD = 0;
  
  @Override
  public void run() {
    /* One entry for each associated predicated */
    Guard[] inputs = {
      vChannel.in(),
      pChannel.in()
    };

    final Alternative services = new Alternative(inputs);
    int chosenService;

    while (true) {
      chosenService = services.fairSelect();

      switch(chosenService){
        case V: 
          ChannelInput ch = vChannel.in();
          vRequest.add((One2OneChannel)ch.read());
          break;

        case P:
          ChannelInput ch_ = pChannel.in();
          pRequest.add((One2OneChannel)ch_.read());
          break;
      }
      /**
       * Unblocking code
       * Must always process all request which is associated CPRE holds
       */      
      boolean anyResumed;
       do {
         anyResumed = false;
         
         int lastItem = vRequest.size();
         for (int i = 0; i < lastItem; i++) {
           One2OneChannel currentV = vRequest.get(QUEUE_HEAD);
           vRequest.remove(QUEUE_HEAD);
           
           if (value < bound){
             //@ assert cpreV();
             value++;
             currentV.out().write(0);
             anyResumed = true; 
           } else {
             vRequest.add(vRequest.size(), currentV);
           }
         }
   
         lastItem = pRequest.size();
         for (int i = 0; i < lastItem; i++) {
           One2OneChannel currentP = pRequest.get(QUEUE_HEAD);
           pRequest.remove(QUEUE_HEAD);
           
           if (value > 0){
             //@ assert cpreP();
             value --;
             currentP.out().write(0);
             anyResumed = true; 
           } else {
             pRequest.add(pRequest.size(), currentP);
           }
         }
         //@ assert vRequest.size() > 0 ==> !cpreV();
         //@ assert pRequest.size() > 0 ==> !cpreP();
       } while (anyResumed);
    }
  }

}
