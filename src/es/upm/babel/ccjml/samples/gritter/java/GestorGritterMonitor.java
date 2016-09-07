package es.upm.babel.ccjml.samples.gritter.java;

import java.util.ArrayList;
import java.util.List;

import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;
import es.upm.babel.cclib.Monitor;

/**
 * Implementacion del Gestor Gritter usando monitores con prioridad 
 * correspondiente a la primera practica de Concurrencia de 2015-2016 
 * 
 * @version 0.1
 * @author Babel Group
 */
public class GestorGritterMonitor implements GestorGritter {

  final int N_USERS;

  /**
   * Guarda quien sigue a quien
   * # = N_USERS * N_USERS
   * siguiendo[A][B] ==> A sigue a B 
   */
  protected Pair<Boolean>[][] siguiendo;
  
  /**
   * Mensajes que aun no han sido escuchados por el usuario
   * # = N_USERS
   */
  protected List<String>[] gritosPorLeer;
  
  private final Monitor mutex;
  
  /**
   * Un usuario esta bloqueado sii no tiene mensajes por leer
   */
  private final Monitor.Cond usuariosEsperandoGritos[];
    
  @SuppressWarnings("unchecked")
  public GestorGritterMonitor(int max){
    this.N_USERS = max;
    
    siguiendo = new Pair [N_USERS][N_USERS];
    for (int i = 0; i < N_USERS; i++) {
      for (int j = 0; j < N_USERS; j++) {
        siguiendo[i][j] = new Pair<Boolean>(false, false);
      }
    }
    
    gritosPorLeer = new List [N_USERS];
    for (int i = 0; i < gritosPorLeer.length; i++) {
      gritosPorLeer[i] = new ArrayList<String>();
    }
    
    mutex = new Monitor();
    usuariosEsperandoGritos = new Monitor.Cond[N_USERS];
    for (int i = 0; i < N_USERS; i++) {
      usuariosEsperandoGritos[i] = mutex.newCond();
    }
  }

  @Override
  public void enviar(int uid, String grito, boolean regrito) {
    // PRE true

    mutex.enter();
    
    // CPRE true
    
    // en base a todos los posibles usuarios que lo esten siguiendo
    // lo agrego a la lista particular de cada seguidor
    for (int i = 0; i < siguiendo[uid].length; i++) {
      if (siguiendo[i][uid].estaSiguiendo() &&
          ((siguiendo[i][uid].leeRegritos() && regrito) ||
           !regrito)
         ){
        if(!gritosPorLeer[i].contains(grito)){ // si no lo tiene, lo agrego
          gritosPorLeer[i].add(grito);
        }
      }
    }
    
    desbloquear();

    mutex.leave();
  }

  @Override
  public void seguir(int seguidor, int seguido, boolean regritos) throws PreViolationSharedResourceException {
    if (seguidor == seguido){
      throw new PreViolationSharedResourceException();
    }
    mutex.enter(); 
    // CPRE true

    // actualizo el nuevo seguidor con sus regritos
    siguiendo[seguidor][seguido].setSiguiendo(true);
    siguiendo[seguidor][seguido].setRegrito(regritos);
    
    mutex.leave();
  }

  @Override
  public void dejarDeSeguir(int seguidor, int seguido) throws PreViolationSharedResourceException {
    // PRE
    if (!siguiendo[seguidor][seguido].estaSiguiendo()){
      mutex.leave();
      throw new PreViolationSharedResourceException();
    }
    
    mutex.enter();
    
    // CPRE true

    // quito el seguidor
    siguiendo[seguidor][seguido].setSiguiendo(false);

    mutex.leave();
    
  }

  @Override
  public String leer(int uid) {
    // PRE true

    mutex.enter();

    // CPRE
    if (gritosPorLeer[uid].isEmpty())
      usuariosEsperandoGritos[uid].await();
    
    String msg = gritosPorLeer[uid].get(0);
    gritosPorLeer[uid].remove(0);

    desbloquear();
    
    mutex.leave();
    return msg;
  }
  
  private void desbloquear() {
    // solo aviso a aquellos usuarios dormidos
    // esperando por leer algo (algo tiene recien puesto)
    for (int i = 0; i < N_USERS; i++) {
      if (!gritosPorLeer[i].isEmpty()  &&
          usuariosEsperandoGritos[i].waiting() > 0
         ){
        usuariosEsperandoGritos[i].signal();
        return;
      }
    }
  }
}