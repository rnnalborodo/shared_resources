package es.upm.babel.ccjml.samples.airport.java;

import java.util.LinkedList;
import java.util.Queue;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;

/** 
 * ControlTower implementation using CSP. 
 * 
 * @author Babel Group
 */ 
public class ControlTowerCSPDeferredRequests extends AControlTower implements CSProcess {

  /** WRAPPER IMPLEMENTATION */
  /**
   *  Channel for receiving external request for each method
   */
  private final Any2OneChannel chBeforeLanding = Channel.any2one();
  private final Any2OneChannel chBeforeTakeOff = Channel.any2one();
  private final Any2OneChannel chAfterLanding  = Channel.any2one();
  private final Any2OneChannel chAfterTakeOff  = Channel.any2one();
  
  /** 
   * List for enqueue all request for each method
   */
  private final Queue<CSPRequest> beforeLandingRequests = new LinkedList<>();
  private final Queue<CSPRequest> beforeTakeOffRequests = new LinkedList<>();
  private final Queue<CSPRequest> afterLandingRequests = new LinkedList<>();
  private final Queue<CSPRequest> afterTakeOffRequests = new LinkedList<>();

  public ControlTowerCSPDeferredRequests(int m) {
    runways = new boolean [m];
  }

  @Override
  public int beforeLanding() {
    //@ assume true;
    One2OneChannel ch = Channel.one2one();
    chBeforeLanding.out().write(new CSPRequest(ch, -1));
    return (int)ch.in().read();
  }

  @Override
  public void afterLanding(int r) {
    //@assume runways[r] && r >=0 && r < runway.length;
    One2OneChannel ch = Channel.one2one();
    chAfterLanding.out().write(new CSPRequest(ch, r));
    ch.in().read();
  }

  @Override
  public int beforeTakeOff() {
    //@ assume true;
    One2OneChannel ch = Channel.one2one();
    chBeforeTakeOff.out().write(new CSPRequest(ch, -1));
    return (int)ch.in().read();
  }

  @Override
  public void afterTakeOff(int r) {
    //@ assume runways[r] && r >=0 && r < runway.length;
    One2OneChannel ch = Channel.one2one();
    chAfterTakeOff.out().write(new CSPRequest(ch, r));
    ch.in().read();
  }

  /** SERVER IMPLEMENTATION */
  /**
   * Constants representing the method presented in the API
   */
  private static final int BEFORE_LANDING = 0;
  private static final int BEFORE_TAKEOFF = 1;
  private static final int AFTER_LANDING = 2;
  private static final int AFTER_TAKEOFF = 3;

  @Override
  public void run() {

    /** One entry for each method */
    Guard[] guards = {
        chBeforeLanding.in(),
        chBeforeTakeOff.in(),
        chAfterLanding.in(),
        chAfterTakeOff.in()
    };

    Alternative services = new Alternative(guards);
    int chosenService = 0;

    int runway;
    One2OneChannel innerCh;

    while (true) {
      
      chosenService = services.fairSelect();
      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0;
      //@ assume syncCond[chosenService];
      
      switch(chosenService){
        case BEFORE_LANDING:
          //@ assert cpreBeforeLanding();
          beforeLandingRequests.offer((CSPRequest) chBeforeLanding.in().read());
          break;
  
        case BEFORE_TAKEOFF:
          //@ assert cpreBeforeTakeOff();
          beforeTakeOffRequests.offer((CSPRequest) chBeforeTakeOff.in().read());
          break;
  
        case AFTER_LANDING: 
          //@ assert true;
          afterLandingRequests.offer((CSPRequest) chAfterLanding.in().read());
          break;
  
        case AFTER_TAKEOFF:
          //@ assert true;
          afterTakeOffRequests.offer((CSPRequest) chAfterTakeOff.in().read());
          break;
      }
      
      CSPRequest request;
      
      //unblocking code
      boolean requestProcessed = true;
      while (requestProcessed) {
        requestProcessed = false;
        int queueSize = beforeLandingRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (cpreBefore()){
            //@ assume cpreBeforeLanding();
            request = beforeLandingRequests.poll(); 
            request.getChannel().out().write(getRunway());
            requestProcessed = true; 
          } else {
            break;
          }
        }
        
        queueSize = beforeTakeOffRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (cpreBefore()){
            //@ assume cpreBeforeTakeOff();
            request = beforeTakeOffRequests.poll();
            request.getChannel().out().write(getRunway());
            requestProcessed = true; 
          }else {
            break;
          }
        }
        
        queueSize = afterLandingRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (true){
            //@ assume true;
            request = afterLandingRequests.poll();
            runways[request.getRunway()] = false; 
            request.getChannel().out().write(null);
            requestProcessed = true;
//          }else {
//            break;
          }
        }
        
        queueSize = afterTakeOffRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (true){
            //@ assume cpreAfterRead();
            request = afterTakeOffRequests.poll();
            runways[request.getRunway()] = false; 
            request.getChannel().out().write(null);
            requestProcessed = true; 
//          } else {
//            break;
          }
        }
        //@ assert (beforeReadRequest.size() > 0 ==> writers > 0)
        //@ assert (afterReadRequest.size() > 0 ==> readers == 0)
        //@ assert (beforeWriteRequest.size() > 0 ==> writers + readers > 0)
        //@ assert (afterWriteRequest.size() > 0 ==> writers == 0)
      }
    } // end while
  } // end run

  //@ requires cpreBeforeLanding && true && repOk();
  //@ ensure \result < runways.length && \result >= 0 && runways[\result];
  private int getRunway(){
    int ra = 0;
    for (int i = 0; i < runways.length; i++) {
      if (!runways[i]){
        ra = i;
        runways[ra] = true;
        break;
      }
    }
    return ra;
  }

}