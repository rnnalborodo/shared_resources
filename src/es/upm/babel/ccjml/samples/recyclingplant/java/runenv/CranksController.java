package es.upm.babel.ccjml.samples.recyclingplant.java.runenv;

import es.upm.babel.ccjml.samples.recyclingplant.java.RecyclingPlant;
import es.upm.babel.cclib.ConcIO;

/**
 * Representing the cranks controller
 * @author rnnalborodo
 */
public class CranksController extends Thread {
  
  private RecyclingPlant cr;
  private int index;

  protected CranksController () { }

  public CranksController (int indice, RecyclingPlant cr) throws Exception {
    this.cr = cr;
    if (indice >= 0 && indice <= Crank.MAX_CRANKS) { 
      this.index = indice;
    } else {
      throw new IllegalArgumentException("Índice de grúa fuera de rango");
    }
  }

  @Override
  public void run () {
    int weight;
    while (true) {
      ConcIO.printfnl("Grua " + index + " inicio recoger.");
      weight = Crank.pick(index);
      ConcIO.printfnl ("Grua " + index + " recogió " + weight);
      cr.notifyWeight(weight);
      ConcIO.printfnl ("Grua " + index + " notifico peso  " + weight);
      cr.incrementWeight(weight);
      ConcIO.printfnl ("Grua " + index + " inicia soltar.");
      Crank.drop(index);
      ConcIO.printfnl ("Grua " + index + " soltó " + weight);
      cr.notifyDrop();
    }
  }
}
