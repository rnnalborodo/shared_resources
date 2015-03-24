package es.upm.babel.ccjml.samples.observer.java.expanded;

//@ model import org.jmlspecs.models.JMLObjectSet;

import java.util.Set;

//@ model import org.jmlspecs.models.JMLObjectSequence;

/** 
 * The Observer design pattern (Chapter 5 of the book Design Patterns by Gamma,
 * Helm, Johnson and Vlissides) is one of the most applied design schemes in
 * programming (reactive systems, interfaces user, etc.). Its operation is based 
 * upon a set of events issued by a component (such as I/O operation, updates 
 * on a ADT), which observers subscribe. When one of these events occurs, all
 * observers subscribed are reported to act accordingly. We have adapted the 
 * pattern so we'll have processes that generates and emit events and processes
 * that subscribe to a subset of them. The formers are listening until one 
 * subscribed event is issued and therefore, react
 * 
 * Listen returns all unlistened events;
 * @author Babel Group 
 */

public interface /*@ shared_resource @*/ EventManagerUpgraded { 
  //@ public model instance JMLObjectSequence subscribed;
  //@ public model instance JMLObjectSequence unlistenedEvents;
  //@ public model instance int N_EVENTS;
  //@ public model instance int N_PROCESSES;

  //@ public instance invariant N_EVENTS > 0 && N_PROCESSES > 0;
  //@ public instance invariant subscribed.length() = N_EVENTS;
  /*@ public instance invariant 
     @        (\forall int i; i >= 0 && i < N_EVENTS; subscribed.get(i).length = N_PROCESSES);
     @*/
  //@ public instance invariant unlistenedEvents.length() = N_EVENTS;
  /*@ public instance invariant 
     @        (\forall int i; i >= 0 && i < N_EVENTS; unlistenedEvents.get(i).length = N_PROCESSES);
     @*/

  //@ public normal_behaviour
  //@   requires eid < N_EVENTS;
  //@   cond_sync true;
  //@   assignable unlistenedEvents.get(eid);
  /*@   ensures    (\forall int i; i >= 0 && i < N_PROCESSES; 
     @                                        unlistenedEvents.get(eid) == subscribed.get(eid));
     @*/
  public void fireEvent(int eid);
  
  //@ public normal_behaviour
  //@   requires eid < N_EVENTS && pid < N_PROCESSES;
  //@   cond_sync true;
  //@   assignable unlistenedEvents.get(eid).get(pid);
  /*@   ensures unlistenedEvents.get(eid).get(pid);
     @*/
  public void subscribe(int pid, int eid);

  //@ public normal_behaviour
  //@   requires eid < N_EVENTS && pid < N_PROCESSES;
  //@   cond_sync true;
  //@   assignable unlistenedEvents.get(eid).get(pid);
  /*@   ensures !unlistenedEvents.get(eid).get(pid);
     @*/
  public void unsubscribe(int pid, int eid);

  //@ public normal_behaviour
  //@   requires eid < N_EVENTS && pid < N_PROCESSES;
  //@   cond_sync (\exists int eid; i < N_EVENTS ; unlistenedEvents.get(i).get(pid));
  //@   assignable unlistenedEvents;
  /*@   ensures  \result = listened && listened.length < N_EVENTS && listened.length >= 0 &&
    @                  (\forall int eid; eid >= 0 && eid < listened.length ; 
    @                                  listened.get(eid)< N_EVENTS && listened.get(eid) >= 0  &&
    @                                  (listened.has(eid) && 
    @                                   unlistenedEvents.get(eid).get(pid) == ! \old(unlistenedEvents.get(eid).get(pid))) ||
    @                                  (! listened.has(eid) && 
    @                                   unlistenedEvents.get(eid).get(pid) == \old(unlistenedEvents.get(eid).get(pid)))
    @                          )
    @                 ;
    @*/
  public Set listen(int pid);
  
}
