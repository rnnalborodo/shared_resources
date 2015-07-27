package es.upm.babel.ccjml.samples.airport.java;

import es.upm.babel.cclib.Monitor;

/** ControlTower implementation using locks and conditions. 
 * 
 * @author Babel Group
 */ 
public class ControlTowerMonitor implements ControlTower {

  //@ public invariant runways.length == monitors.length;
  private /*@ spec_public @*/boolean runways[];
  private Monitor monitors[];
  
  private Monitor selectorMonitor;
  private Monitor.Cond waitingPlanes;
  
  //@ ensures \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  private /*@ pure @*/ boolean cpreBeforeLanding(){
    return cpreBefore();
  }
  
  //@ ensures \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  private /*@ pure @*/ boolean cpreBeforeTakeOff(){
    return cpreBefore();
  }
  
  //@ ensures \result == (\exists int i; i >= 0 && i < monitor.length; runways[i]);
  private /*@ pure @*/ boolean cpreBefore(){
    for (int i = 0; i < monitors.length; i++) {
      if (!runways[i]){
        return true;
      }
    }
    return false;
  }
  
  //@ requires r >=0 && r < runways.length;
  //@ ensures runways[r]; 
  private /*@ pure @*/ boolean preBeforeLanding(int r){
    return runways[r] && r >=0 && r < runways.length;
  }
  
  //@ requires r >=0 && r < runways.length;
  //@ ensures runways[r]; 
  private /*@ pure @*/ boolean preBeforeTakeOff(int r){
    return runways[r] && r >=0 && r < runways.length;
  }
  
  
  public ControlTowerMonitor(int m) {
    runways = new boolean [m];
    monitors = new Monitor[m];
    
    for (int i = 0; i < monitors.length; i++) {
      runways[i] = false;
      monitors[i] = new Monitor();
    }
    
    selectorMonitor = new Monitor();
    waitingPlanes = selectorMonitor.newCond();
  }
  
  @Override
  public int beforeLanding() {
    selectorMonitor.enter();
    //@ assume true; 
    if (!cpreBeforeLanding())
      waitingPlanes.await();
    
    //@ assume cpreBeforeLanding && true && repOk();
    int ra = 0;
    for (int i = 0; i < monitors.length; i++) {
      if (!runways[i]){
        ra = i;
        runways[ra] = true;
        break;
      }
    }
    
    // no waken up can be performed
    // due to we are taken runways
    
    selectorMonitor.leave();
    return ra;
  }

  @Override
  public void afterLanding(int r) {
    monitors[r].enter();
    //@ assume runways[r] && r >=0 && r < runway.length;
    if (!true)
      waitingPlanes.signal();
    
    runways[r] = false;
    
    if (waitingPlanes.waiting() > 0)
      selectorMonitor.enter();
      waitingPlanes.signal();
      selectorMonitor.leave();

    
    monitors[r].leave();
  }

  @Override
  public int beforeTakeOff() {
    selectorMonitor.enter();
    //@ assume true; 
    if (!cpreBeforeTakeOff())
      waitingPlanes.await();
    
    //@ assume cpreBeforeLanding && true && repOk();
    int ra = 0;
    for (int i = 0; i < monitors.length; i++) {
      if (!runways[i]){
        ra = i;
        runways[ra] = true;
        break;
      }
    }
    
    // no waken up can be performed
    // due to we are taken runways
    
    selectorMonitor.leave();
    return ra;
  }

  @Override
  public void afterTakeOff(int r) {
    monitors[r].enter();
    //@ assume runways[r] && r >=0 && r < runway.length;
    if (!true)
      waitingPlanes.await();
    
    runways[r] = false;
    
    if (waitingPlanes.waiting() > 0){
      selectorMonitor.enter();
      waitingPlanes.signal();
      selectorMonitor.leave();
    }
    
    monitors[r].leave();
  }
  
  /*@
  @ public normal_behavior
  @   ensures true;
  @*/ 
  protected /*@ pure @*/ boolean repOk(){
    return true;
  }
 
}
