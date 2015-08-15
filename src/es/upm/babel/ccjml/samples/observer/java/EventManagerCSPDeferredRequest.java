package es.upm.babel.ccjml.samples.observer.java;

import java.util.LinkedList;
import java.util.Queue;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.AltingChannelInput;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.readerswriters.java.Request;

/** 
 * Observer implementation CSP with deferred request processing. 
 * 
 * @author Babel Group
 */ 
public class EventManagerCSPDeferredRequest extends AEventManager implements CSProcess {

  /** WRAPPER IMPLEMENTATION */ 
  /**
   *  Channel for receiving external request for each method
   */
  Any2OneChannel chFireEvent   = Channel.any2one();
  Any2OneChannel chSubscribe   = Channel.any2one();
  Any2OneChannel chUnsubscribe = Channel.any2one();
  Any2OneChannel chListen      = Channel.any2one();
  
  /** 
   * List for enqueue all request for each method
   */
  private final Queue<Request<Integer>> fireEventRequests   = new LinkedList<>();
  private final Queue<Request<int[]>>   subscribeRequests   = new LinkedList<>();
  private final Queue<Request<int[]>>   unsubscribeRequests = new LinkedList<>();
  private final Queue<Request<Integer>> listenRequests      = new LinkedList<>();
  
  public EventManagerCSPDeferredRequest(int maxEvents, int maxProcesses){
    subscribed = new boolean [maxEvents][maxProcesses];
    unlistenedEvents = new boolean [maxEvents][maxProcesses];
 
  }
  
  @Override
  public void fireEvent(int eid) {
    //@ assume preFireEvent(eid) && repOk();
    One2OneChannel innerChannel = Channel.one2one();
    chFireEvent.out().write(
                          new Request<Integer>(innerChannel,eid));
    innerChannel.in().read();
  }

  @Override
  public void subscribe(int pid, int eid) {
    //@ assume preSubscribe(pid,eid) && repOk();
    One2OneChannel innerChannel = Channel.one2one();
    chSubscribe.out().write(
                          new Request<int[]>(innerChannel,new int[]{pid, eid}));
    innerChannel.in().read();
  }

  @Override
  public void unsubscribe(int pid, int eid) {
    //@ assume preUnsuscribe(pid, eid) && repOk();
    One2OneChannel innerChannel = Channel.one2one();
    chUnsubscribe.out().write(
                          new Request<int[]>(innerChannel,new int[]{pid, eid}));
    innerChannel.in().read();
  }

  @Override
  public int listen(int pid) {
    //@ assume preListen(pid) && repOk();
    One2OneChannel innerChannel = Channel.one2one();
    chListen.out().write(
                          new Request<Integer>(innerChannel,pid));
    // data to be returned
    return (Integer)innerChannel.in().read();
  }

  /* SERVER IMPLEMENTATION */
  /** Constants representing API method's */
  final int FIRE_EVENT  = 0;
  final int SUBSCRIBE   = 1;
  final int UNSUBSCRIBE = 2;
  final int LISTEN      = 3;
  
  @SuppressWarnings("unchecked")
  public void run() {
    /* One entry for each method. */
    final Guard[] guards = new AltingChannelInput[4];
    guards[FIRE_EVENT]  = chFireEvent.in();
    guards[SUBSCRIBE]   = chSubscribe.in();
    guards[UNSUBSCRIBE] = chUnsubscribe.in();
    guards[LISTEN]      = chListen.in();

    final Alternative services = new Alternative(guards);
    int chosenService;

    while (true) {
      
      chosenService = services.fairSelect();
      
      switch (chosenService) {
        case FIRE_EVENT:
          fireEventRequests.offer((Request<Integer>)chFireEvent.in().read());
          break;

        case SUBSCRIBE:
          subscribeRequests.offer((Request<int[]>)chSubscribe.in().read());
          break;
          
        case UNSUBSCRIBE:
          unsubscribeRequests.offer((Request<int[]>)chUnsubscribe.in().read());
          break;
          
        case LISTEN:
          listenRequests.offer((Request<Integer>)chListen.in().read());
          break;
      }
      
      /**
       * Unblocking code
       * Must always process all request which is associated CPRE holds
       */
      Request<Integer> request;
      Request<int[]> requestPID;
      boolean requestProcessed = true;
      while (requestProcessed) {
        requestProcessed = false;
        
        // CPRE does not depends on the parameters
        int queueSize = fireEventRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (true){
            //@ assert true;
            request = fireEventRequests.poll();
            this.innerFireEvent(request.getFootprint()); 
            request.getChannel().out().write("");
            requestProcessed = true; 
//          } else {
//            break;
          }
        }
        
        // CPRE does not depends on the parameters
        queueSize = subscribeRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (true){
            //@ assert true;
            requestPID = subscribeRequests.poll();
            this.innerSubscribe(requestPID.getFootprint()[0], 
                                requestPID.getFootprint()[1]); 
            requestPID.getChannel().out().write("");
            requestProcessed = true; 
//          }else {
//            break;
          }
        }
        
        // CPRE does not depends on the parameters
        queueSize = unsubscribeRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (true){
            //@ asser true;
            requestPID = unsubscribeRequests.poll();
            this.innerUnsubscribe(requestPID.getFootprint()[0], 
                                  requestPID.getFootprint()[1]); 
            requestPID.getChannel().out().write("");
            requestProcessed = true; 
//          }else {
//            break;
          }
        }
        
        /**
         * CPRE depends on parameters
         * We must check each of the request
         */
        queueSize = listenRequests.size();
        for(int i = 0; i < queueSize;i++) {
          request = listenRequests.poll();
          if (cpreListen(request.getFootprint())){
            //@ assert cpreAfterRead();
            int result = this.innerListen(request.getFootprint()); 
            request.getChannel().out().write(result);
            requestProcessed = true; 
          } else {
            // this request cannot be processed right now
            listenRequests.offer(request);
          }
        }        
      }
    } // end while
  } // end run

  
  //@ requires true && cpreFireEvent(eid);
  public void innerFireEvent(int eid) {
    System.arraycopy(subscribed[eid], 0, unlistenedEvents[eid], 0, subscribed[eid].length);
  }

  //@ requires true && cpreSubscribe(pid, eid);
  public void innerSubscribe(int pid, int eid) {
    subscribed[eid][pid]=true;
  }

  //@ requires true && cpreUnsubscribe(pid, eid);
  public void innerUnsubscribe(int pid, int eid) {
    subscribed[eid][pid]=false;
  }

  //@ requires preListen(pid) && cpreListen(pid);
  public int innerListen(int pid) {
    int listened = 0;
    for (int eid = 0; eid < unlistenedEvents.length && listened == 0 ; eid++) {
        if (unlistenedEvents[eid][pid]){
          unlistenedEvents[eid][pid] = false;
          listened = eid;
        }
    }
    return listened;
  }  

}
