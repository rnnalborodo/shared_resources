package es.upm.babel.ccjml.samples.observer.java.key;

/** Observer implementation using locks and conditions. 
 * 
 * @author Babel Group
 */ 
public class EventManagerMonitorKeY {
  
  private final int N_EIDS = 3;
  private final int N_PIDS = 11;

  
  /*@ public invariant
     @         unlistenedEvents.length == N_EIDS &&
     @         (\forall int i; i >= 0 && i < N_EIDS; unlistenedEvents[i].length == NPIDs);
     @*/
  private final boolean[][] unlistenedEvents = new boolean[N_EIDS][N_PIDS];
  private final boolean[][] subscribed = new boolean[N_EIDS][N_PIDS];
    
  /*@ public invariant
     @         processWaitingForEvent.length == N_PIDS && 
     @         (\forall int i; i >= 0 && i < N_PIDS; processWaitingForEvent[i] >= 0);
     @*/
  private int[] processWaitingForEvent;
  
  /*@ ensures */
  private boolean cpreListen(int pid) {
    for (boolean[] unlistenedEvent : unlistenedEvents) {
      if (unlistenedEvent[pid]) {
        return true;
      }
    }
    return false;
  }
  
  
//  @Override
//  public void fireEvent(int eid) {
//    mutex.enter();
//    System.arraycopy(subscribed[eid], 0, unlistenedEvents[eid], 0, subscribed[eid].length);
//    
//    unblockBasedOnEvent(eid);
//    
//    mutex.leave();
//  }
//
//  @Override
//  public void subscribe(int pid, int eid) {
//    mutex.enter();
//    subscribed[eid][pid]=true;
//    //hacer falta copia de los unlistened para que le subscriptor este 
//    //pendiente de los eventos emitidos anteriormente?
//    mutex.leave();
//  }
//
//  @Override
//  public void unsubscribe(int pid, int eid) {
//    mutex.enter();
//    subscribed[eid][pid]=false;
//    mutex.leave();
//  }
//
//  @Override
//  public int listen(int pid) {
//    mutex.enter();
//    if (!cpreListen(pid)){
//      processWaitingForEvent[pid].await();
//    }
//    
//    int listened = 0;
//    for (int eid = 0; eid < unlistenedEvents.length && listened == 0 ; eid++) {
//        if (unlistenedEvents[eid][pid]){
//          unlistenedEvents[eid][pid] = false;
//          listened = eid;
//        }
//    }
//    
//    // unblocking code
//    for (int i = 0; i < unlistenedEvents.length; i++) {
//      //  unblocking code based on the received event
//      if (unblockBasedOnEvent(i))
//        break;
//    }
//    
//    //deber'ia bloquearlo de nuevo para que siga escuchando 
//    //por los otros eventos o consumir todos los eventos de una pasada
//    mutex.leave();
//    
//    return listened;
//  }
//
//  private boolean unblockBasedOnEvent(int eid) {
//    //  unblocking code based on the received event
//    for (int pid = 0; pid < unlistenedEvents[eid].length; pid++) {
//      if (unlistenedEvents[eid][pid] && processWaitingForEvent[pid].waiting() > 0){
//        processWaitingForEvent[pid].signal();
//        return true;
//      }
//    }
//    return false;
//  }

}
