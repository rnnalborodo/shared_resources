package es.upm.babel.ccjml.samples.airport.java;

import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;

/** 
 * Implementation of ControlTower using synchronized methods 
 *
 * @author Babel Group 
 */

public class ControlTowerSync extends AControlTower{

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

    return ra;
  }

  @Override
  public synchronized void afterLanding(int r) throws PreViolationSharedResourceException {
    if (! preAfterLanding(r))
      throw new PreViolationSharedResourceException("afterLanding");
    //@ assume preAfterLanding(r);
//    while (!true)
//      this.wait();
    //@ assert true;
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

    //@ assert cpreBeforeTakeOff() && true && repOk();
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
  public synchronized void afterTakeOff(int r) throws PreViolationSharedResourceException {
    if (! preAfterTakeOff(r))
      throw new PreViolationSharedResourceException("afterTakeOff");
    //@ assume preAfterTakeOff(r);
//    while (!true)
//      this.wait();
    //@ assert true;
    runways[r] = false;

    notifyAll();
  }
}


