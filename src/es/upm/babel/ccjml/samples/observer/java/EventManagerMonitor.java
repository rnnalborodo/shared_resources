package es.upm.babel.ccjml.samples.observer.java;

import es.upm.babel.cclib.Monitor;

/** 
 * Observer implementation using locks and conditions. 
 * 
 * @author Babel Group
 */ 
public class EventManagerMonitor extends AEventManager {
  
  private final Monitor mutex;
  private final Monitor.Cond processWaitingForEvent[];
    
  public EventManagerMonitor(int maxEvent, int maxProcesses){
    subscribed = new boolean [maxEvent][maxProcesses];
    unlistenedEvents = new boolean [maxEvent][maxProcesses];
    
    mutex = new Monitor();
    processWaitingForEvent = new Monitor.Cond[maxProcesses];
    for (int i = 0; i < maxProcesses; i++) {
      processWaitingForEvent[i] = mutex.newCond();
    }
  }
  
  @Override
  public void fireEvent(int eid) {
    mutex.enter();
    //@ assume preFireEvent(eid) && repOk(); 
    //if (!true){}
    //@ assert preFireEvent(eid) && cpreFireEvent(eid) && repOk();
    System.arraycopy(subscribed[eid], 0, unlistenedEvents[eid], 0, subscribed[eid].length);
    
    unblockBasedOnEvent(eid);
    mutex.leave();
  }

  @Override
  public void subscribe(int pid, int eid) {
    mutex.enter();
    //@ assume preSubscribe(pid, eid) && repOk(); 
    //if (!true){}
    //@ assert preSubscribe(pid, eid) && cpreSubscribe(eid) && repOk();
    subscribed[eid][pid]=true;
    
    mutex.leave();
  }

  @Override
  public void unsubscribe(int pid, int eid) {
    mutex.enter();
    //@ assume preUnsubscribe(pid, eid) && repOk(); 
    //if (!true){}
    //@ assert preUnsubscribe(pid, eid) && cpreUnsubscribe(eid) && repOk();
    subscribed[eid][pid]=false;
    
    mutex.leave();
  }

  @Override
  public int listen(int pid) {
    mutex.enter();
    //@ assume preListe(pid) && repOk();
    if (!cpreListen(pid)){
      processWaitingForEvent[pid].await();
    }
    //@ assert preListen(pid) && cpreListen(pid) && repOk();
    
    int listened = 0;
    for (int eid = 0; eid < unlistenedEvents.length && listened == 0 ; eid++) {
        if (unlistenedEvents[eid][pid]){
          unlistenedEvents[eid][pid] = false;
          listened = eid;
        }
    }
    
    // unblocking code
    for (int i = 0; i < unlistenedEvents.length; i++) {
      //  unblocking code based on the received event
      if (unblockBasedOnEvent(i) != -1 )
        break;
    }
    //@ assert only one thread is awake
    
    mutex.leave();
    
    return listened;
  }

  //@ requires validEventId(eid);
  //@ assignable processWaitingForEvent[*];
  //@ ensures validProcessId(\result) || \result == -1;
  //@ ensures processWaitingForEvent[\result].waiting() + 1 == \old(processWaitingForEvent[\result]).waiting();
  /*@ ensures (\forall int i ; i < processWaitingForEvent.length && i >= 0; 
    @                        (i != \result ==> 
    @                                     processWaitingForEvent[i] == 
    @                                          \old(processWaitingForEvent[i]));
    @*/ 
  private int unblockBasedOnEvent(int eid) {
    //  unblocking code based on the received event
    for (int pid = 0; pid < unlistenedEvents[eid].length; pid++) {
      if (unlistenedEvents[eid][pid] && processWaitingForEvent[pid].waiting() > 0){
        processWaitingForEvent[pid].signal();
        return pid;
      }
    }
    return -1;
  }

}
