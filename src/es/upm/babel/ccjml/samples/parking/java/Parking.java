package es.upm.babel.ccjml.samples.parking.java;

/**
 * Parking slot in a building. (Add complexity, give a slot number at entering.)
 * 
 * @author rnnalborodo
 */
public interface /*@ shared_resource @*/ Parking {
    //@ public model instance int slots;
    //@ public model instance int MAX;
  
    //@ public instance invariant slots >= 0 && slots <= MAX;
    //@ public instance invariant MAX > 0;

    //@ public initially slots == 0;

    //@ public normal_behaviour
    //@   cond_sync slots < MAX ;
    //@   assignable data;
    //@   ensures data == \old(data).concat(JMLObjectSequence
    //@                                     .convertFrom(els));
    public void enter();

    //@ public normal_behaviour
    //@   requires n <= maxData / 2;
    //@   cond_sync n <= nData();
    //@   assignable data;
    //@   ensures    \result.length == n
    //@           && JMLObjectSequence.convertFrom(\result)
    //@                               .concat(data)
    //@               == \old(data);
    public void leave();
}
