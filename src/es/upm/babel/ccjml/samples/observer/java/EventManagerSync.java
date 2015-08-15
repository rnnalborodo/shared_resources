package es.upm.babel.ccjml.samples.observer.java;

import java.util.logging.Level;
import java.util.logging.Logger;

/** Implementation of Observer using synchronization methods 
 *
 * @author Babel Group 
 */

public class EventManagerSync extends AEventManager { 
  
  public EventManagerSync(int maxEvent, int maxProcesses){
    subscribed = new boolean [maxEvent][maxProcesses];
    unlistenedEvents = new boolean [maxEvent][maxProcesses];
  }
  
  @Override
  public synchronized void fireEvent(int eid) {
    //@ assume preFireEvent(eid) && repOk(); 
    //while (!true){
    //  wait();
    //}
    //@ assert preFireEvent(eid) && true && repOk();
    System.arraycopy(subscribed[eid], 0, unlistenedEvents[eid], 0, subscribed[eid].length);
    notifyAll();
  }

  @Override
  public synchronized void subscribe(int pid, int eid) {
    //@ assume preSubscribe(eid) && repOk(); 
    //while (!true){
    //  wait();
    //}
    //@ assert  preSubscribe(eid) && true && repOk();
    subscribed[eid][pid]=true;
  }

  @Override
  public synchronized void unsubscribe(int pid, int eid) {
    //@ assume preUnsubscribe(eid) && repOk(); 
    //while (!true){
    //  wait();
    //}
    //@ assert preUnsubscribe(eid) && true && repOk();
    subscribed[eid][pid]=false;
  }

  @Override
  public synchronized int listen(int pid) {
    //@ assume preListen(pid) && repOk();
    while (!cpreListen(pid)){
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(EventManagerSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    }
    //@ assert preListen(pid) && cpreListen(pid) && repOk();
    int found = 0;
    for (int eid = 0; eid < unlistenedEvents.length && found == 0 ; eid++) {
        if (unlistenedEvents[eid][pid]){
          unlistenedEvents[eid][pid] = false;
          found = eid;
        }
    }
    notifyAll();
    return found;
  }

}
