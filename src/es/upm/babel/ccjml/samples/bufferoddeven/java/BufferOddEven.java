package es.upm.babel.ccjml.samples.bufferoddeven.java;
//@ model import org.jmlspecs.models.JMLObjectSequence;

/**
 * Likewise a bounded buffer. Producer processes add new elements (natural numbers in this example) to the 
 * buffer, and consumer processes remove elements from it. Items are read from the external world and written 
 * back to it.
 * 
 * @author BABEL Group
 */

public interface /*@ shared_resource @*/ BufferOddEven {

  public enum Type { EVEN, ODD }
  
  //@ public model instance JMLObjectSequence data;
  //@ public model instance int MAX;

  //@ public instance invariant MAX > 0;
  //@ public instance invariant data.length() <= MAX;

  //@ public initially data.length() == 0;
  //@ public initially MAX > 0;

  //@ public normal_behaviour
  //@   requires true;
  //@   cond_sync data.length <= MAX - 1;
  //@   assignable data;
  //@   ensures data == \old(data).insertBack(n);
  public void put(int n);

  //@ public normal_behaviour
  //@   requires true;
  //@   cond_sync data.length > 0 && ((data.get(0) % 2 == 0 && t == EVEN) || (data.get(0) % 2 == 1 && t == ODD));
  //@   assignable data;
  //@   ensures \result == \old(data).get(0) && \old(data) == data.insertFront(\result);
  public int get(Type t);
}
