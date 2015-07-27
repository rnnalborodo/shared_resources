package es.upm.babel.ccjml.samples.airport.java;


/** Implementation of ControlTower using syncrhonization methods 
 *
 * @author Babel Group 
 */

public class ControlTowerSync implements ControlTower {


  //@ public invariant runways.length == monitors.length;
  private /*@ spec_public @*/boolean runways[];

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
    for (int i = 0; i < runways.length; i++) {
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


  public ControlTowerSync(int m) {
    runways = new boolean [m];
  }

  @Override
  public synchronized int beforeLanding() {
    //@ assume true; 
    while (!cpreBeforeLanding())
      try {
        this.wait();
      } catch (InterruptedException e) {
        e.printStackTrace();
      }

    //@ assume cpreBeforeLanding && true && repOk();
    int ra = 0;
    for (int i = 0; i < runways.length; i++) {
      if (!runways[i]){
        ra = i;
        runways[ra] = true;
        break;
      }
    }

    // no waken up can be performed
    // due to we are taken runways

    return ra;
  }

  @Override
  public synchronized void afterLanding(int r) {
    //@ assume runways[r] && r >=0 && r < runway.length;
//    while (!true)
//      this.wait();

    runways[r] = false;

    notifyAll();
  }

  @Override
  public synchronized int beforeTakeOff() {
    //@ assume true; 
    while (!cpreBeforeTakeOff())
      try {
        this.wait();
      } catch (InterruptedException e) {
        e.printStackTrace();
      }

    //@ assume cpreBeforeLanding && true && repOk();
    int ra = 0;
    for (int i = 0; i < runways.length; i++) {
      if (!runways[i]){
        ra = i;
        runways[ra] = true;
        break;
      }
    }

    // no waken up can be performed
    // due to we are taken runways

    return ra;
  }

  @Override
  public synchronized void afterTakeOff(int r) {
    //@ assume runways[r] && r >=0 && r < runway.length;
//    while (!true)
//      this.wait();

    runways[r] = false;

    notifyAll();
  }

  /*@
    @ public normal_behavior
    @   ensures true;
    @*/ 
  protected /*@ pure @*/ boolean repOk(){
    return true;
  }

}


