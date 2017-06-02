package es.upm.babel.cclib;

/**
 * Monitor simplification for code verification in KeY.
 */
public class Monitor {

  //@ public instance variable mutex;
  private boolean mutex = false;


  /*@ public normal_behaviour
    @  requires !this.mutex; 
    @  assignable mutex;
    @  ensures this.mutex;
    @*/
  public void enter() {
    // TODO check  taken - block - busy waiting?
    this.mutex = true;
  }

  /**
   * Leaves the monitor.
   */
  /*@ public normal_behaviour
    @  requires this.mutex; 
    @  assignable mutex;
    @  ensures !this.mutex;
    @*/
  public void leave() {
    mutex = false;
  }

  /**
   * Returns a new condition associated to this monitor.
   */
  public Cond newCond() {
    return new Cond();
  }

  /**
   * Conditions.
   */
  public class Cond {
    private int waiting;

    //@ public instance invariant waiting >= 0;
    //@ public initially waiting == 0;

    //    private Cond() {
    //      waiting = 0;
    //    }

    /*@ public normal_behaviour 
      @  assignable waiting;
      @  ensures waiting = old(waiting) + 1;
      @*/
    public void await() {
      waiting++;
    }


    /*@ public normal_behaviour 
      @  requires waiting > 1;
      @  assignable waiting;
      @  ensures waiting = old(waiting) - 1;
      @*/
    public void signal() {
      waiting--;
    }

    //  /*@ public normal_behaviour
    //    @  assignable waiting; 
    //    @  ensures waiting = 0;
    //    @*/
    //    private void signalAll() {
    //      waiting = 0;
    //    }

    /*@ public normal_behaviour
      @  ensures \result == waiting;
      @*/
    public /*@ pure @*/int waiting() {
      return waiting;
    }
  }
}
