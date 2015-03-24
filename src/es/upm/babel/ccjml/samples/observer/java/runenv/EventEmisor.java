package es.upm.babel.ccjml.samples.observer.java.runenv;

import es.upm.babel.ccjml.samples.observer.java.EventManager;
import es.upm.babel.cclib.ConcIO;

public class EventEmisor extends Thread
{
  private EventManager ge;
  private final int eid;

  public EventEmisor(EventManager ge,
                int eid) {
    this.ge = ge;
    this.eid = eid;
  }

  public void run() {
    while (true) {
      try {
        Thread.sleep(1000 * (eid + 1));
      } catch (Exception ex) {
        ConcIO.printfnl("excepción capturada: " + ex);
        ex.printStackTrace();
      }
      ConcIO.printfnl("Emitiendo evento " + eid);
      ge.fireEvent(eid);
    }
  }
}
