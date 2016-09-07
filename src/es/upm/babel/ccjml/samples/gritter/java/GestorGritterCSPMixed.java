package es.upm.babel.ccjml.samples.gritter.java;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.AltingChannelInput;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;
import es.upm.babel.ccjml.samples.utils.Tuple;

/**
 * Implementacion del Gestor Gritter usando monitores con prioridad 
 * correspondiente a la primera practica de Concurrencia de 2015-2016 
 * 
 * @version 0.1
 * @author Babel Group
 */
public class GestorGritterCSPMixed implements CSProcess, GestorGritter {

  /** WRAPPER IMPLEMENTATION */
  /**
   * canales para recibir las peticiones
   */
  Any2OneChannel chSeguir = Channel.any2one();
  Any2OneChannel chDejarDeSeguir = Channel.any2one();
  Any2OneChannel chEnviar = Channel.any2one();
  Any2OneChannel chLeer = Channel.any2one();

  public GestorGritterCSPMixed() {}

  @Override
  public void enviar(int uid, String grito, boolean regrito) {
    // PRE true
    chEnviar.out().write(new Tuple<Integer, Tuple<String, Boolean>>(uid, new Tuple<String,Boolean>(grito, regrito)));
  }

  @Override
  public void seguir(int seguidor, int seguido, boolean regritos) 
                      throws PreViolationSharedResourceException {
    // PRE
    if (seguidor == seguido) {
      throw new PreViolationSharedResourceException();
    }
    // enviar footprint de la invocacion junto con el canal auxiliar
    chSeguir.out().write(new Tuple<Integer, Tuple<Integer, Boolean>>
                                  (seguidor, new Tuple<Integer,Boolean>(seguido, regritos)));

  }

  @Override
  public void dejarDeSeguir(int seguidor, int seguido) 
                      throws PreViolationSharedResourceException {
    // PRE a comprobar en el servidor
    One2OneChannel innerChannel = Channel.one2one();

    chDejarDeSeguir.out().write(new RequestGritter<Integer, Integer>(innerChannel, seguidor, seguido));
    // espero respuesta por PRE - si lo que lee es una instancia de excepcion, la lanzo
    Object obj = innerChannel.in().read();
    if (obj instanceof PreViolationSharedResourceException){
      throw (PreViolationSharedResourceException)obj;
    }
  }

  @Override
  public String leer(int pid) {
    // PRE
    One2OneChannel innerChannel = Channel.one2one();
    // enviar footprint de la invocacion junto con el canal auxiliar
    chLeer.out().write(new Tuple<One2OneChannel,Integer>(innerChannel, pid));
    // para recibir el grito leido desde el servidor
    String grito = innerChannel.in().read().toString();
    return grito;
  }

  /* SERVER IMPLEMENTATION */
  /** Constants representing API method's */
  final int ENVIAR = 0;
  final int SEGUIR = 1;
  final int DEJARDESEGUIR = 2;
  final int LEER = 3;

  @SuppressWarnings("unchecked")
  public void run() {
    
    /**
     * Guarda quien sigue a quien
     */
    Map<Integer, Set<Pair<Integer>>> siguiendo = new HashMap<>();;

    /**
     * Mensajes que aun no han sido escuchados por el usuario
     */
    Map<Integer, Set<String>> gritosPorLeer = new HashMap<>();
    /**
     * listas de peticiones aplazadas
     */
    final Queue<Tuple<One2OneChannel,Integer>> leerRequests = new LinkedList<>();    
    /* One entry for each method. */
    final Guard[] guards = new AltingChannelInput[4];
    guards[ENVIAR] = chEnviar.in();
    guards[SEGUIR] = chSeguir.in();
    guards[DEJARDESEGUIR] = chDejarDeSeguir.in();
    guards[LEER] = chLeer.in();

    final Alternative services = new Alternative(guards);
    int chosenService = -1;

    
    while (true) {
      chosenService = services.fairSelect();
      RequestGritter<Integer, Integer> request;
      int seguidor;
      int seguido;

      switch (chosenService) {
      case ENVIAR:

        Tuple<Integer, Tuple<String, Boolean>> requestEnviar = 
                                        (Tuple<Integer, Tuple<String, Boolean>>) chEnviar.in().read();
        
        // siempre puedo procesar enviar
        // @assert true;
        int userid = requestEnviar.getFst();
        String grito = requestEnviar.getSnd().getFst();
        Boolean regrito = requestEnviar.getSnd().getSnd();
        // primero busco los seguidores
        Set<Integer> seguidores = new HashSet<>();
        for (Entry<Integer, Set<Pair<Integer>>> currentSeguidor : siguiendo.entrySet()) {
          for (Pair<Integer> current : currentSeguidor.getValue()) {
            if (current.estaSiguiendo() == userid && ((regrito && current.leeRegritos()) || !regrito)) {
              seguidores.add(currentSeguidor.getKey());
            }
          }
        }

        // ahora que tengo los seguidores, hago broadcast
        for (Integer currentSeguidor : seguidores) {
          if (gritosPorLeer.get(currentSeguidor) == null) { // creo contenedor de gritos
            gritosPorLeer.put(currentSeguidor, new HashSet<String>());
          }
          gritosPorLeer.get(currentSeguidor).add(grito);
        }
        break;

      case SEGUIR:
        Tuple<Integer, Tuple<Integer, Boolean>> requestSeguir = 
                                                  (Tuple<Integer, Tuple<Integer, Boolean>>) chSeguir.in().read();
        seguidor = requestSeguir.getFst();
        seguido = requestSeguir.getSnd().getFst();
        boolean regritos = requestSeguir.getSnd().getSnd();

        // si aun no existe el usuario creo el set asociado y agrego el par
        if (!siguiendo.containsKey(seguidor)) {
          siguiendo.put(seguidor, new HashSet<Pair<Integer>>());
        }

        Pair<Integer> value = null;
        // ya existe el set de seguidores, cambio los regritos
        for (Pair<Integer> current : siguiendo.get(seguidor)) {
          if (current.estaSiguiendo() == seguido) {
            current.setRegrito(regritos);
            value = current;
            break;
          }
        }

        if (value == null) { // no estaba siguiendo
          // creo y agrego el par nuevo
          value = new Pair<Integer>(seguido, regritos);
          siguiendo.get(seguidor).add(value);
        }
        
        break;

      case DEJARDESEGUIR:
        // encolar la nueva peticion si se cumple la PRE
        request = (RequestGritter<Integer, Integer>) chDejarDeSeguir.in().read();
        seguidor = request.getSnd();
        seguido = request.getThird();
        // PRE
        Pair<Integer> seguidorPair = null;
        if (siguiendo.get(seguidor)!= null){
          for (Pair<Integer> current : siguiendo.get(seguidor)) {
            if (current.estaSiguiendo() == seguido) {
              seguidorPair = current;
              break;
            }
          }
        }
        
        if (seguidorPair == null) { // hay ecxcepcion - no agrego la peticion a la lista
          request.getChannel().out().write(new PreViolationSharedResourceException());
        } else { // no hay excepcion
          // notifico al wrapper que no hay excepcion y encolo la peticion
          for (Pair<Integer> current : siguiendo.get(seguidor)) {
            if (current.estaSiguiendo() == seguido) {
              siguiendo.get(seguidor).remove(current);
              request.getChannel().out().write(null);
              break;
            }
          }
        }

        break;

      case LEER:
        // encolar la nueva peticion
        leerRequests.add((Tuple<One2OneChannel,Integer>) chLeer.in().read());
//        break;
      } // end switch

      /**
       * codigo de procesamiento de Leer, debe procesar todas aquellas peticiones que su
       * CPRE es cierta
       */
      // procesar peticiones LEER si y solo si las operarcion ejecutada fue
      // LEER o ENVIAR
      if (chosenService == LEER || chosenService == ENVIAR) {
        if (!leerRequests.isEmpty()) {
          LinkedList<Tuple<One2OneChannel,Integer>> requestsToRemove = new LinkedList<Tuple<One2OneChannel,Integer>>();
          for (Tuple<One2OneChannel,Integer> leerRequest : leerRequests) {
            int uid = leerRequest.getSnd();
            
            if (gritosPorLeer.get(uid) != null && !gritosPorLeer.get(uid).isEmpty()) {
              // remuevo el item
              requestsToRemove.add(leerRequest);
              // @ assert this.gritosPorLeer.get(uid) != null && !this.gritosPorLeer.get(uid).isEmpty();
              
              // leo el mensaje que haya - no importa orden
              String grito = gritosPorLeer.get(uid).iterator().next();
              gritosPorLeer.get(uid).remove(grito);
              //aviso invocador que termino de procesar
              leerRequest.getFst().out().write(grito);
            }
          }
          // removing processed requests
          leerRequests.removeAll(requestsToRemove);
        }
      }
    }// end while server
  } // end run
}