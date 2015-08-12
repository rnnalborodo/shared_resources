package es.upm.babel.ccjml.samples.airport.java;


/** Implementation of ControlTower using synchronization methods 
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
    //@ assume preAfterLanding(r);
//    while (!true)
//      this.wait();
    //@ assume true;
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

    //@ assume cpreBeforeTakeOff() && true && repOk();
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
    //@ assume preAfterTakeOff(r);
//    while (!true)
//      this.wait();

    runways[r] = false;

    notifyAll();
  }
}


