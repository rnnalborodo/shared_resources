package es.upm.babel.ccjml.samples.boundedbuffer.java;
/**
 * A variation of a producer-consumer problem using a buffer of only ONE element in which Producers add 
 * new items to the buffer whilst consumers get and remove a given number of items.
 * 
 * @author rnnalborodo
 */
//@ model import org.jmlspecs.models.JMLObjectSequence;

public interface /*@ shared_resource @*/ BoundedBuffer {
  
  //@ public model instance JMLObjectSequence data;
  //@ public model instance int MAX;

  //@ public instance invariant MAX > 0;
  //@ public instance invariant data.length() <= MAX;

  //@ public initially data.length() == 0;
  //@ public initially MAX > 0;

  //@ public normal_behaviour
  //@   requires true;
  //@   cond_sync data.length() <= MAX - 1;
  //@   assignable data;
  //@   ensures data == \old(data).insertBack(n);
  public void put(int n);

  //@ public normal_behaviour
  //@   requires true;
  //@   cond_sync data.length() > 0;
  //@   assignable data;
  //@   ensures \result == \old(data).get(0) && \old(data) == data.insertFront(\result);
  public int get();
  
}