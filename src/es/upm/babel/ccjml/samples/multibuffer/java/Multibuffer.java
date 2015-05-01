package es.upm.babel.ccjml.samples.multibuffer.java;

//@ model import org.jmlspecs.models.JMLObjectSequence;

/**
 * A variation of a producer-consumer problem using a bounded buffer in which Producers add new items to 
 * the buffer whilst consumers get and remove a given number of items.
 * 
 * @author rnnalborodo
 */
public interface /*@ shared_resource @*/ Multibuffer {
    //@ public model instance JMLObjectSequence data;
    //@ public model instance int maxData;

    //@ public instance invariant maxData > 0;
    //@ public instance invariant data.length() <= maxData;

    //@ public initially data.length() == 0;
    //@ public initially maxData > 0;

    //@ public normal_behaviour
    //@   ensures \result == maxData;
    public int maxData();

    //@ public normal_behaviour
    //@   ensures \result == data.length();
    //@ public model pure int nData();

    //@ public normal_behaviour
    //@   ensures \result == maxData - data.length();
    //@ public model pure int nSlots();

    //@ public normal_behaviour
    //@   requires els.length <= maxData / 2;
    //@   cond_sync els.length <= nSlots();
    //@   assignable data;
    /*@   ensures data == \old(data)
      @                      .concat(JMLObjectSequence.convertFrom(els));
      @*/
    public void put(Object[] els);

    //@ public normal_behaviour
    //@   requires n <= maxData / 2;
    //@   cond_sync n <= nData();
    //@   assignable data;
    /*@   ensures \result.length == n && 
      @            JMLObjectSequence.convertFrom(\result)
      @                      .concat(data) == \old(data);
      @*/
    public Object[] get(int n);
}
