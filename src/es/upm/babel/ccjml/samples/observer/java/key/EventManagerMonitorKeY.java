package es.upm.babel.ccjml.samples.observer.java.key;

/** Observer implementation using locks and conditions. 
 * 
 * @author Babel Group
 */ 
public class EventManagerMonitorKeY {

  //@ public invariant N_EIDS == 2;
  private final int N_EIDS = 2;
  //@ public invariant N_PIDS == 2;
  private final int N_PIDS = 2;

  /*@ public invariant
    @          unlistenedEvents.length == N_EIDS &&
    @          (\forall int i; i >= 0 && i < N_EIDS; 
    @                    unlistenedEvents[i].length == N_PIDS);
    @*/
  private boolean[][] unlistenedEvents;
    
  // instrument a condition as an integer
  /* public invariant
     @         processWaitingForEvent.length == N_PIDS && 
     @         (\forall int i; i >= 0 && i < N_PIDS; 
     @                  processWaitingForEvent[i] >= 0);
     @*/
  private int[] processWaitingForEvent;
  
  //prop_signal_0_1
  //@ public invariant signaled == 0 || signaled == 1;
  private int signaled;

  /*@ public normal_behavior
    @   requires pid >= 0 && pid < N_PIDS;
    @   ensures unlistenedEvents[\result][pid] || \result == -1;
    @*/
  private /*@ pure @*/ int cpreListenInt(int pid) {
    int i= 0;
    /* loop_invariant
      @   0<=i && i< N_EIDS ;
      @ decreases N_EIDS - i;
      @*/
    while ( i < N_EIDS) {
      if (unlistenedEvents[i][pid]) {
        return i;
      }
      i++;
    }
    return -1;
  }

  /*@ public normal_behavior
    @   requires pid >= 0 && pid < N_PIDS;
    @   ensures \result == (\exists int i; i >= 0 && i < N_EIDS;
    @                                               unlistenedEvents[i][pid]);
    @*/
  private /*@ pure @*/ boolean cpreListen(int pid) {
    int i= 0;
    /* loop_invariant
      @   0<=i && i< N_EIDS ;
      @ decreases N_EIDS - i;
      @*/
    while ( i < N_EIDS) {
      if (unlistenedEvents[i][pid]) {
        return true;
      }
      i++;
    }
    return false;
  }

  /*@ public normal_behavior
    @   requires pid >= 0 && pid < N_PIDS;
    @   ensures \result == (\exists int i; i >= 0 && i < N_EIDS;
    @                                               unlistenedEvents[i][pid]);
    @*/
  private /*@ pure @*/ boolean cpreListenWithCpreInside(int pid) {
    return cpreListenInt(pid) != -1;
  }
  
  //@ requires pid >= 0 && pid < N_PIDS;
  //@ assignable processWaitingForEvent[*], signaled;
  //prop_signal_0_1
  /* ensures 
    @    (\forall int i; i >= 0 && i < processWaitingForEvent.length;
    @         processWaitingForEvent[i] == \old(processWaitingForEvent)[i])
    @    ||
    @    (\exists int i; i >= 0 && i < processWaitingForEvent.length;
    @         processWaitingForEvent[i] == \old(processWaitingForEvent)[i] - 1 
    @     &&
    @     (\forall int j; j >= 0 && j < processWaitingForEvent.length; i == j ||
    @         processWaitingForEvent[j] == \old(processWaitingForEvent)[j])
    @    );
    @*/
  // prop_signal_effective
  /*@ public normal_behavior
    @    ensures 
    @     signaled == 1 ==>
    @     (\exists int i; i >= 0 && i < processWaitingForEvent.length;
    @          processWaitingForEvent[i] == \old(processWaitingForEvent)[i] -1);
    @*/
  // ensures (\exists int i; i >= 0 && i < N_PIDS; processWaitingForEvent[i] == \old(processWaitingForEvent)[i] -1 );
  private void unblock(int eid) {
    signaled = 0;
    //  unblocking code based on the received event
    for (int pid = 0; pid < N_PIDS; pid++) {
      if (unlistenedEvents[eid][pid] && processWaitingForEvent[pid] > 0){
        processWaitingForEvent[pid]--;
        signaled ++;
        return;
      }
    }
  }

}
