package es.upm.babel.ccjml.samples.mergesort.java;

import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;

public class  MergeSortCompSync <T extends Comparable> implements MergeSortComp<Comparable<Object>>{

  Comparable<Object> left;
  Comparable<Object> right;
    
  public synchronized void setLeft(Comparable<Object> obj) throws PreViolationSharedResourceException {
    if (!(obj != null))
      throw new PreViolationSharedResourceException();
    
    //@ assume obj != null;
    while (! (this.left == null))
      try {wait();
      } catch (InterruptedException e) {}
    
    //@ assert this.left == null;
    this.left = obj;
    
    //@ assert this.left == obj;
    notifyAll();
  }

  public void setRight(Comparable<Object> obj) throws PreViolationSharedResourceException {
    if (!(obj != null))
      throw new PreViolationSharedResourceException();
    
    //@ assume obj != null;
    while (! (this.right == null))
      try {wait();
      } catch (InterruptedException e) {}
    
    //@ assert this.right == null;
    this.right = obj;
    
    //@ assert this.right == obj;
    notifyAll();

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
    while (! (left !=null && right != null))
      try {wait();
      } catch (InterruptedException e) {}
    
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
    notifyAll();
    return res;
  }
}
