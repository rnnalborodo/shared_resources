package es.upm.babel.ccjml.samples.readerswriters.java;

public interface /* shared_resource @*/ ReadersWriters {
  //@ public model instance int readers;
  //@ public model instance int writers;
  
  /*@ public instance invariant 
    @    readers >= 0 && writers >= 0 &&
    @    (readers > 0 ==> writers == 0) &&
    @    (writers > 0 ==> readers == 0 && writers == 1);
    @*/
  
  //@ public initially readers == 0 && writers == 0;
  
  /*@ public normal_behaviour
    @   cond_sync writers + readers == 0;
    @   assignable writers;
    @   ensures writers > 0;
    @*/
  public void beforeWrite();
  
  /*@ public normal_behaviour
    @   requires writers == 1;
    @   assignable writers;
    @   ensures writers == 0;
    @*/
  public void afterWrite();
  
  /*@ public normal_behaviour
    @   cond_sync writers == 0;
    @   assignable readers;
    @   ensures readers == \old(readers) -1;
    @*/
  public void beforeRead();
  
  /*@ public normal_behaviour
    @   requires readers > 0;
    @   assignable readers;
    @   ensures readers == \old(readers) -1;
    @*/
  public void afterRead();
}
