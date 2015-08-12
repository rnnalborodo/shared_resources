package es.upm.babel.ccjml.samples.readerswriters.java;

public abstract class AReadersWriters implements ReadersWriters {

  protected int readers = 0;
  protected int writers = 0;
  
  //@ public normal_behaviour
  //@   ensures \result == (writers + readers == 0);  
  protected /*@pure@*/ boolean cpreBeforeWrite() {
    return readers == 0 && writers == 0 ;
  }

  //@ public normal_behaviour
  //@   ensures \result == writers == 0;
  protected boolean /*@ pure @*/cpreBeforeRead() {
    return writers ==0;
  }
  
  
  @Override
  public String toString(){
    return "RW = [ reader = " + readers + " | writers= " + writers + "]";
  }
  
  /*@ ensures  \result == readers >= 0 && writers >= 0 &&
    @                     (readers > 0 ==> writers == 0) &&
    @                     (writers > 0 ==> readers == 0 && writers == 1);
    @*/     
  public boolean repOk(){
    return readers >= 0 && writers >= 0 &&
           ((readers > 0 && writers == 0) ||
           (writers > 0 && readers == 0 && writers == 1));
  }

}
