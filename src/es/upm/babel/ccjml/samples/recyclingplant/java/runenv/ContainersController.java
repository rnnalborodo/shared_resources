package es.upm.babel.ccjml.samples.recyclingplant.java.runenv;

import java.util.Calendar;

import es.upm.babel.ccjml.samples.recyclingplant.java.RecyclingPlant;
import es.upm.babel.cclib.ConcIO;

public class ContainersController extends Thread {
  private RecyclingPlant cr;

  // max weight supported by the container
  private static final int MIN_WEIGHT = Crank.MIN_W_CRANK + 1000;

  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());

  protected ContainersController () {
  }

  public ContainersController (RecyclingPlant cr) {
      this.cr = cr;
  }

  @Override
  public void run () {
    while (true) {
      cr.prepareReplacement();
      ConcIO.printfnl("Contenedor preparado");
      ConcIO.printfnl("Inicio de sustitución");
      Container.replace();
      ConcIO.printfnl("Fin de sustitución");
      int w = random.nextInt(MIN_WEIGHT)+MIN_WEIGHT;
      cr.notifyReplacement(w);
      ConcIO.printfnl("New container of weight "+w+" installed");
      // Retardo para provocar potenciales entrelazados
      try {
        Thread.sleep(100);
      } catch (InterruptedException x) {
        x.printStackTrace();
      }
    }
  }
}
