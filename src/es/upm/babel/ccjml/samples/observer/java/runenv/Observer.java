package es.upm.babel.ccjml.samples.observer.java.runenv;

import es.upm.babel.ccjml.samples.observer.java.EventManager;
import es.upm.babel.cclib.ConcIO;

public class Observer extends Thread
{
  private final EventManager ge;
  private final int pid;

  public Observer(EventManager ge,int pid) {
    this.ge = ge;
    this.pid = pid;
  }

  @Override
  public void run() {
    while (true) {
      
      int n = 2;
      int eid;
      
      for (int i = 0; i < n; i++) {
        eid = (pid + i) % EventManagerRunner.N_EVENTS;
        ConcIO.printfnl("Proceso " + pid + " subscrito a evento " + eid);
        ge.subscribe(pid, eid);
      }
      for (int i = 0; i < n; i++) {
        ConcIO.printfnl("Proceso " + pid + " escuchando...");
        eid = ge.listen(pid);
        ConcIO.printfnl("Evento " + eid + " escuchado!");
        ge.unsubscribe(pid,eid);
        ConcIO.printfnl("Proceso " + pid + " desubscrito de evento " + eid);
      }
      
      try {
        Thread.sleep(499);
      } catch (Exception ex) {
        ConcIO.printfnl("excepción capturada: " + ex);
        ex.printStackTrace();
      }
    }
  }
}
