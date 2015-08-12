package es.upm.babel.ccjml.samples.observer.java;

import java.util.Arrays;

public abstract class AEventManager implements EventManager {
  
  protected boolean[][] subscribed;
  protected boolean[][] unlistenedEvents;
  
  //@ requires eid < subscribed.length && pid < subscribed[0].length;
  //@ requires eid >= 0 && pid >= 0;
  //@ ensures (\exists int i; i < subscribed.length && i >= 0 ;unlistenedEvents[i][pid]);
  protected /*@ pure @*/ boolean cpreListen(int pid) {
    for (boolean[] unlistenedEvent : unlistenedEvents) {
      if (unlistenedEvent[pid]) {
        return true;
      }
    }
    return false;
  }
  
  @Override
  public String /*@ pure @*/ toString(){
    return "subscribed=" + Arrays.deepToString(subscribed) + 
           "\nunlistenedEvents = "+ Arrays.deepToString(unlistenedEvents);
  }
  
  /*@ ensures (\forall int i; i < subscribed.length && i >= 0 ;
    @              (\forall int j ; j < subscribed[i].length && j >= 0;
    @                   unlistenedEvents[i][j] ==> subscribed [i][j])));
    @*/
  public boolean /*@ pure @*/ repOk() {
    for (int i = 0; i < subscribed.length; i++) {
      for (int j = 0; j < subscribed.length; j++) {
        if (unlistenedEvents[i][j] && !subscribed[i][j])
          return false;
      }
    }
    return true;
  }
  
  //@ ensures pid >= 0 && pid < subscribed[0].length;
  protected boolean /*@ pure @*/ validProcessId(int pid){
    return pid >= 0 && pid < subscribed[0].length;
  }
  
  //@ ensures eid >= 0 && eid < subscribed.length;
  protected boolean /*@ pure @*/ validEventId(int eid){
    return eid >= 0 && eid < subscribed.length;
  }
  
  //@ ensures pid >= 0 && pid < subscribed[0].length;
  //@ ensures eid >= 0 && eid < subscribed.length;
  public boolean /*@ pure @*/ preSubscribed(int eid, int pid){
    return validProcessId(pid) && validEventId(eid);
  }

  //@ ensures pid >= 0 && pid < subscribed[0].length;
  //@ ensures eid >= 0 && eid < subscribed.length;
  public boolean /*@ pure @*/ preUnsubscribed(int eid, int pid){
    return validProcessId(pid) && validEventId(eid);
  }
  
  //@ ensures eid >= 0 && eid < subscribed.length;
  public boolean /*@ pure @*/ preFireEvent(int eid){
    return validEventId(eid);
  }

  //@ ensures pid >= 0 && pid < subscribed[0].length;
  public boolean /*@ pure @*/ preListen(int pid){
    return validProcessId(pid);
  }
}
