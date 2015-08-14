package es.upm.babel.ccjml.samples.airport.java;

import es.upm.babel.cclib.Monitor;

/** ControlTower implementation using locks and conditions. 
 * 
 * @author Babel Group
 */ 
public class ControlTowerMonitor extends AControlTower {

  private Monitor monitors[];

  private Monitor selectorMonitor;
  private Monitor.Cond waitingPlanes;

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

    //@ assert cpreBeforeLanding && true && repOk();
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
    //    if (!true)
    //      waitingPlanes.signal();

    //@ assert true;
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

    //@ assert cpreBeforeLanding && true && repOk();
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
    //    if (!true)
    //      waitingPlanes.await();

    //@ assert true;
    runways[r] = false;

    if (waitingPlanes.waiting() > 0){
      selectorMonitor.enter();
      waitingPlanes.signal();
      selectorMonitor.leave();
    }

    monitors[r].leave();
  }
}
