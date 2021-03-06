package es.upm.babel.ccjml.samples.airport.java;

import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;
import es.upm.babel.cclib.Monitor;


/** 
  * ControlTower implementation using monitors. 
  * 
  * @author rul0
  */ 
public class ControlTowerMonitor extends AControlTower {

  private Monitor mutex;
  private Monitor.Cond waitingPlanes;

  public ControlTowerMonitor(int m) {
    runways = new boolean [m];
    mutex = new Monitor();
    waitingPlanes = mutex.newCond();
  }

  @Override
  public int beforeLanding() {
    mutex.enter();
    //@ assume true; 
    if (!cpreBeforeLanding())
      waitingPlanes.await();

    //@ assert cpreBeforeLanding() && true && repOk();
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
    mutex.leave();
    return ra;
  }

  @Override
  public void afterLanding(int r) throws PreViolationSharedResourceException {
    mutex.enter();
    
    if (! preAfterLanding(r))
      throw new PreViolationSharedResourceException("afterLanding");
    //@ assume runways[r] && r >=0 && r < runways.length;
    //    if (!true)
    //      waitingPlanes.signal();

    //@ assert true;
    runways[r] = false;

    if (waitingPlanes.waiting() > 0)
      waitingPlanes.signal();
    
    mutex.leave();
  }

  @Override
  public int beforeTakeOff() {
    mutex.enter();
    //@ assume true; 
    if (!cpreBeforeTakeOff())
      waitingPlanes.await();

    //@ assert cpreBeforeLanding() && true && repOk();
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

    mutex.leave();
    return ra;
  }

  @Override
  public void afterTakeOff(int r) throws PreViolationSharedResourceException {    
    mutex.enter();
    if (! preAfterLanding(r))
      throw new PreViolationSharedResourceException("afterLanding");

    //@ assume runways[r] && r >=0 && r < runways.length;
    //    if (!true)
    //      waitingPlanes.await();

    //@ assert true;
    runways[r] = false;

    if (waitingPlanes.waiting() > 0){
      mutex.enter();
      waitingPlanes.signal();
      mutex.leave();
    }

    mutex.leave();
  }
}
