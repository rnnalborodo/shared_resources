package es.upm.babel.ccjml.samples.mergesort.java;

import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;
import es.upm.babel.cclib.Monitor;

public class MergeSortCompMonitor <T extends Comparable> implements MergeSortComp<Comparable<Object>>{

  private Monitor mutex;
  private Monitor.Cond leftCond;
  private Monitor.Cond rightCond;
  private Monitor.Cond bothCond;
  
  Comparable<Object> left;
  Comparable<Object> right;
    
  public MergeSortCompMonitor(){
    this.mutex = new Monitor();
    this.leftCond = mutex.newCond();
    this.rightCond = mutex.newCond();
    this.bothCond = mutex.newCond();
  }
  
  public synchronized void setLeft(Comparable<Object> obj) throws PreViolationSharedResourceException {
    if (!(obj != null))
      throw new PreViolationSharedResourceException();
    
    //@ assume obj != null;
    if (! (this.left == null))
      leftCond.await();
    
    //@ assert this.left == null;
    this.left = obj;
    
    //@ assert this.left == obj;
    dummyUnblockingCode();
  }

  public void setRight(Comparable<Object> obj) throws PreViolationSharedResourceException {
    if (!(obj != null))
      throw new PreViolationSharedResourceException();
    
    //@ assume obj != null;
    if (! (this.right == null))
      rightCond.await();
    
    //@ assert this.right == null;
    this.right = obj;
    
    //@ assert this.right == obj;
    dummyUnblockingCode();

  }
  
  /*@ public normal_behaviour
    @   requires true;
    @   cond_sync right != null && left != null;
    @   assignable right, left;
    @   ensures (\result == left &&  left.comparteTo(right) < 0 && 
    @                         left == null && right == \old(right)) ||
    @           (\result == right &&  left.comparteTo(right) >= 0 && 
    @                          right == null && left == \old(left));
    @*/
  public Comparable<Object> getResult(){
    
    //@ assume true;
    if (! (left !=null && right != null))
      bothCond.await();
    
    //@ assert left !=null && right != null;
    Comparable<Object> res;
    if (left.compareTo(right) < 0){
      res = left;
      left = null;
    } else {
      res = right;
      right = null;
    }
    
    /*@ assert (res == left &&  left.comparteTo(right) < 0 && 
      @                         left == null && right == \old(right)) ||
      @        (res == right &&  left.comparteTo(right) >= 0 && 
      @                          right == null && left == \old(left)); 
      @*/
    dummyUnblockingCode();
    return res;
  }
  
  public void dummyUnblockingCode(){
    if (right == null && rightCond.waiting()>0)
      rightCond.signal();
    else if (left == null && leftCond.waiting()>0)
      leftCond.signal();
    else if (left != null && right != null && bothCond.waiting() > 0)
      bothCond.signal();
  }
}
