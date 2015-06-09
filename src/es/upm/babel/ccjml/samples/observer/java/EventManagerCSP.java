package es.upm.babel.ccjml.samples.observer.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.AltingChannelInput;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

/** 
 * Observer implementation using JCSP Library with channel expansion.  
 * 
 * @author Babel Group
 */ 
public class EventManagerCSP extends AEventManager implements CSProcess {

  /** SHARED RESOURCE IMPLEMENTATION */
  private final int N_PIDS;

  /** WRAPPER IMPLEMENTATION */
  /**
   *  Channel for receiving external request for each method
   */
  Any2OneChannel fireEventChannel;
  Any2OneChannel subscribeChannel;
  Any2OneChannel unsubscribeChannel;
  One2OneChannel[] listenChannel;
  
  public EventManagerCSP(int maxEvents, int maxProcesses){
    subscribed = new boolean [maxEvents][maxProcesses];
    unlistenedEvents = new boolean [maxEvents][maxProcesses];

    N_PIDS = maxProcesses;
    
    fireEventChannel   = Channel.any2one();
  	subscribeChannel   = Channel.any2one();
  	unsubscribeChannel = Channel.any2one();
  	
  	listenChannel  = new One2OneChannel[N_PIDS];
  	for (int pid = 0; pid < N_PIDS; pid++) {
  	    listenChannel[pid] = Channel.one2one();
  	}
  }
  
  @Override
  public void fireEvent(int eid) {
    //@ assume preFireEvent(eid) && repOk();
    fireEventChannel.out().write(eid);
  }

  @Override
  public void subscribe(int pid, int eid) {
    //@ assume preSubscribe(pid,eid) && repOk();
    subscribeChannel.out().write(new Tuple<Integer,Integer>(pid, eid));
  }

  @Override
  public void unsubscribe(int pid, int eid) {
    //@ assume preUnsuscribe(pid, eid) && repOk();
    unsubscribeChannel.out().write(new Tuple<Integer,Integer>(pid, eid));
  }

  @Override
  public int listen(int pid) {
    //@ assume preListen(pid) && repOk();
    One2OneChannel innerChannel = Channel.one2one();
    listenChannel[pid].out().write(innerChannel);
    // data to be returned
    return ((Integer) innerChannel.in().read());
  }
  
  /** SERVER IMPLEMENTATION */
  /**
   * Constants representing the method presented in the API
   */
  final int FIRE_EVENT  = 0;
  final int SUBSCRIBE   = 1;
  final int UNSUBSCRIBE = 2;
  
  @SuppressWarnings("unchecked")
  public void run() {
    // Constants representing the method presented in the API

    /**
     *  One entry for each method.
     *  Due to the fact that cpreListen() depends on 'pid', 
     *  we create channels as many 'pid' we can have for
     *  selective reception,i.e., #channels = N_PID + 3  
     */
    final Guard[] guards = new AltingChannelInput[N_PIDS + 3];
    guards[FIRE_EVENT]  = fireEventChannel.in();
    guards[SUBSCRIBE]   = subscribeChannel.in();
    guards[UNSUBSCRIBE] = unsubscribeChannel.in();
    for (int pid = 0; pid < N_PIDS; pid++) {
        guards[pid+3] = listenChannel[pid].in();
    }
    
    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean[] sincCond = new boolean[N_PIDS + 3];
    sincCond[FIRE_EVENT] = sincCond[SUBSCRIBE] = sincCond[UNSUBSCRIBE] = true;
    for (int i = 3; i < sincCond.length; i++) {
      sincCond[i] = false;
    }

    final Alternative services = new Alternative(guards);
    int chosenService;
    /**
     *  Server loop
     */
    while (true) {
      
      for (int i = 3; i < sincCond.length; i++) {
        sincCond[i] = cpreListen(i-3);
      }
      sincCond[0] = true;
      sincCond[1] = true;
      sincCond[2] = true;
      /*@ assume (\forall int i; i >= 3 & i < syncCond.length; 
        @           syncCond[i] ==> cpreListen(i-3)) &&
        @        (\forall int i; i >= 0 & i < 3; 
        @           syncCond[i] ==> true)
        @*/
      
      chosenService = services.fairSelect(sincCond);
      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0;
      //@ assume syncCond[chosenService];
      
      Tuple<Integer,Integer> request; 
      
      switch (chosenService) {
        case FIRE_EVENT:
          //@ assume true;
          int eid = (Integer)fireEventChannel.in().read();
          innerFireEvent(eid);
          break;

        case SUBSCRIBE:
        //@ assume true;
          request = (Tuple<Integer,Integer>)subscribeChannel.in().read();
          innerSubscribe(request.getFst(), request.getSnd());
          break;
          
        case UNSUBSCRIBE:
          //@ assume true;
          request = (Tuple<Integer, Integer>)unsubscribeChannel.in().read();
          innerUnsubscribe(request.getFst(), request.getSnd());
          break;
          
        // Listen invocation processing
        default:
          //@ assume cpreListen(chosenService -3);
          One2OneChannel channel = ((One2OneChannel)listenChannel[chosenService-3].in().read());
          eid = innerListen(chosenService-3);
          channel.out().write(eid);
          break;
      }
    }
  }
  
  //@ requires eid < N_EVENTS && eid >= 0;
  //@ cond_sync true;
  //@ assignable unlistenedEvents.get(eid);
  /*@ ensures (\forall int i; i >= 0 && i < N_PROCESSES;
    @                        unlistenedEvents.get(eid) == subscribed.get(eid));
    @*/
  public void innerFireEvent(int eid) {
    System.arraycopy(subscribed[eid], 0, unlistenedEvents[eid], 0, subscribed[eid].length);
  }

  //@ public normal_behaviour
  //@ requires pid >=0  && pid < N_PROCESSES;
  //@ requires eid >= 0 && pid < N_EVENTS;
  //@ assignable ((JMLObjectSequence)unlistenedEvents.get(eid)).get(pid);
  //@ ensures ((JMLObjectSequence)unlistenedEvents.get(eid)).get(pid);
  public void innerSubscribe(int pid, int eid) {
    subscribed[eid][pid]=true;
  }

  //@ requires pid >=0  && pid < N_PROCESSES;
  //@ requires eid >= 0 && pid < N_EVENTS;
  //@ assignable ((JMLObjectSequence)unlistenedEvents.get(eid)).get(pid);
  //@ ensures !unlistenedEvents.get(eid).get(pid);
  public void innerUnsubscribe(int pid, int eid) {
    subscribed[eid][pid]=false;
  }
  
  //@ public normal_behaviour
  //@ requires pid < N_EVENTS && pid < N_PROCESSES;
  //@ cond_sync (\exists int eid; i < N_EVENTS ;((JMLSequence) unlistenedEvents.get(i)).get(pid));
  //@ assignable unlistenedEvents;
  /*@ ensures \result < N_EVENTS && \result >= 0 && 
    @ ((JMLObjectSequence)unlistenedEvents.get(\result)).get(pid) == 
    @                  !\old(((JMLObjectSequence)unlistenedEvents.get(\result)).get(pid)) &&
    @ (\forall int i; i < N_EVENTS ;((JMLObjectSequence)unlistenedEvents.get(i)).get(pid) == false &&
    @               ((JMLObjectSequence)unlistenedEvents.get(\result)).get(pid) == 
    @               \old(((JMLObjectSequence)unlistenedEvents.get(\result)).get(pid))
    @               || i == \result
    @ );
    @*/
  public int innerListen(int pid) {
    int found = 0;
    for (int eid = 0; eid < unlistenedEvents.length && found == 0 ; eid++) {
        if (unlistenedEvents[eid][pid]){
          unlistenedEvents[eid][pid] = false;
          found = eid;
        }
    }
    return found;
  }  

}
