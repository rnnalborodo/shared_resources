package es.upm.babel.ccjml.samples.mergesort.java;

public interface  MergeSortComp <T extends Comparable>{

  //@ public model instance T left;
  //@ public model instance T right;
  
  //@ public initially left == right && right == null;
  
  /*@ public normal_behaviour
    @   requires obj !=null;
    @   cond_sync left == null;
    @   assignable left;
    @   ensures left == obj;
    @*/
  public void setLeft(T obj);

  /*@ public normal_behaviour
    @   requires obj !=null;
    @   cond_sync right == null;
    @   assignable right;
    @   ensures right == obj;
    @*/
  public void setRight(T obj);
  
  /*@ public normal_behaviour
    @   requires true;
    @   cond_sync right != null && left != null;
    @   assignable right, left;
    @   ensures (\result == left &&  left.comparteTo(right) < 0 && 
    @                         left == null && right == \old(right)) ||
    @           (\result == right &&  left.comparteTo(right) >= 0 && 
    @                          right == null && left == \old(left));
    @*/
  public T getResult();
}
