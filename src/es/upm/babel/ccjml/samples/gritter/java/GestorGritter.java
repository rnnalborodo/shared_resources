package es.upm.babel.ccjml.samples.gritter.java;

import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;

//@ model import org.jmlspecs.models.JMLObjectSet;
//@ model import org.jmlspecs.models.JMLObjectSequence;

/**
  * Interface of GestorGritter. JML description
  * 
  * @author Babel Group
  */
public interface GestorGritter {

  //@ public model instance JMLObjectSequence siguiendo;
  //@ public model instance JMLObjectSequence regritos;
  //@ public model instance int N_USERS;

  //@ public instance invariant N_USERS > 0;
  //@ public instance invariant siguiendo.length == N_USERS;
  //@ public instance invariant siguiendo.length == N_USERS;
  
  /*@ public instance invariant
    @ (\forall int i; i >= 0 && i < N_EVENTS; subscribed.get(i).length == N_PROCESSES);
    @*/
  //@ public instance invariant unlistenedEvents.length == N_EVENTS;
  /*@ public instance invariant
    @ (\forall int i; i >= 0 && i < N_EVENTS;
    @            ((JMLObjectSequence)unlistenedEvents.get(i)).length == N_PROCESSES);
    @*/
  public void enviar(int uid, String grito, boolean regrito);
  
  /*@  public normal_behavior
    @    requires seguidor == seguido;
    @    assignable \nothing;
    @    ensures \result > z;
    @ also
    @  public exceptional_behavior
    @    requires seguidor == seguido;
    @    assignable \nothing;
    @    signals (PreViolationSharedResourceException) true;
    @*/
  public void seguir(int seguidor, int seguido, boolean regritos) 
                                     throws PreViolationSharedResourceException;

  /*@  public normal_behavior
    @    requires seguidor == seguido;
    @    assignable \nothing;
    @    ensures \result > z;
    @ also
    @  public exceptional_behavior
    @    requires seguidor == seguido;
    @    assignable \nothing;
    @    signals (PreViolationSharedResourceException) true;
    @*/
  public void dejarDeSeguir(int pid, int eid) 
                                     throws PreViolationSharedResourceException;


  public String leer(int pid);

}
