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

import es.upm.babel.ccjml.samples.observer.java.Request;
import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;

/**
 * Implementacion de Gritter usando CSP con peticiones aplazadas
 * 
 * @author Babel Group
 */
public class GestorGritterCSPDeferredRequests implements CSProcess, GestorGritter {

  /** WRAPPER IMPLEMENTATION */
  /**
   * canales para recibir las peticiones
   */
  Any2OneChannel chSeguir = Channel.any2one();
  Any2OneChannel chDejarDeSeguir = Channel.any2one();
  Any2OneChannel chEnviar = Channel.any2one();
  Any2OneChannel chLeer = Channel.any2one();

  public GestorGritterCSPDeferredRequests() {}

  @Override
  public void enviar(int uid, String grito, boolean regrito) {
    // PRE true
    One2OneChannel innerChannel = Channel.one2one();
    // enviar footprint de la invocacion junto con el canal auxiliar
    chEnviar.out().write(new RequestGritter<String, Boolean>(innerChannel, grito, regrito));

    innerChannel.out().write(uid);
    // para recibir respuesta desde el servidor
    innerChannel.in().read();
  }

  @Override
  public void seguir(int seguidor, int seguido, boolean regritos) throws PreViolationSharedResourceException {
    // PRE
    if (seguidor == seguido) {
      throw new PreViolationSharedResourceException();
    }
    One2OneChannel innerChannel = Channel.one2one();
    // enviar footprint de la invocacion junto con el canal auxiliar
    chSeguir.out().write(new RequestGritter<Integer, Integer>(innerChannel, seguidor, seguido));

    innerChannel.out().write(regritos);
    // para recibir respuesta desde el servidor
    innerChannel.in().read();
  }

  @Override
  public void dejarDeSeguir(int seguidor, int seguido) throws PreViolationSharedResourceException {
    // PRE a comprobar en el servidor
    One2OneChannel innerChannel = Channel.one2one();
    chDejarDeSeguir.out().write(new RequestGritter<Integer, Integer>(innerChannel, seguidor, seguido));
    // espero respuesta por PRE - si lo que lee es una instancia de excepcion, la lanzo
    Object obj = innerChannel.in().read();
    if (obj instanceof PreViolationSharedResourceException){
      throw (PreViolationSharedResourceException)obj;
    }
    // enviar footprint de la invocacion junto con el canal auxiliar
    // para recibir respuesta desde el servidor
    innerChannel.in().read();
  }

  @Override
  public String leer(int pid) {
    // PRE
    One2OneChannel innerChannel = Channel.one2one();
    // enviar footprint de la invocacion junto con el canal auxiliar
    chLeer.out().write(new Request<Integer>(innerChannel, pid));
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
    final Queue<RequestGritter<Integer, Integer>> seguirRequests = new LinkedList<>();
    final Queue<RequestGritter<Integer, Integer>> dejarDeSeguirRequests = new LinkedList<>();
    final Queue<RequestGritter<String, Boolean>> enviarRequests = new LinkedList<>();
    final Queue<Request<Integer>> leerRequests = new LinkedList<>();

    
    /* One entry for each method. */
    final Guard[] guards = new AltingChannelInput[4];
    guards[ENVIAR] = chEnviar.in();
    guards[SEGUIR] = chSeguir.in();
    guards[DEJARDESEGUIR] = chDejarDeSeguir.in();
    guards[LEER] = chLeer.in();

    final Alternative services = new Alternative(guards);
    int chosenService;

    while (true) {

      chosenService = services.fairSelect();

      RequestGritter<Integer, Integer> object;
      switch (chosenService) {
      case ENVIAR:
        // encolar la nueva peticion
        enviarRequests.add((RequestGritter<String, Boolean>) chEnviar.in().read());
        break;

      case SEGUIR:
        // encolar la nueva peticion
        seguirRequests.add((RequestGritter<Integer, Integer>) chSeguir.in().read());
        break;

      case DEJARDESEGUIR:
        // encolar la nueva peticion si se cumple la PRE
        object = (RequestGritter<Integer, Integer>) chDejarDeSeguir.in().read();
        int seguidor = object.getSnd();
        int seguido = object.getThird();
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
          object.getChannel().out().write(new PreViolationSharedResourceException());
        } else { // no hay excepcion
          // notifico al wrapper que no hay excepcion y encolo la peticion
          object.getChannel().out().write(null);
          dejarDeSeguirRequests.add(object);
        }

        break;

      case LEER:
        // encolar la nueva peticion
        leerRequests.add((Request<Integer>) chLeer.in().read());
        break;
      }

      /**
       * codigo de desbloqueo, debe procesar todas aquellas peticiones que su
       * CPRE es cierta
       */
      // procesar peticiones SEGUIR
      // no hace falta bucle
      if (!seguirRequests.isEmpty()) {
        // remuevo el item
        RequestGritter<Integer, Integer> request = seguirRequests.poll();
        // @ assert true;

        int seguidor = request.getSnd();
        int seguido = request.getThird();
        boolean regritos = (boolean) request.getChannel().in().read();

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
        
        //aviso invocador
        request.getChannel().out().write(null);
      }

      // procesar peticiones DEJARDESEGUIR
      // no hace falta bucle
      if (!dejarDeSeguirRequests.isEmpty()) {
        // remuevo el item
        RequestGritter<Integer, Integer> request = dejarDeSeguirRequests.poll();
        // @ assert true;

        int seguidor = request.getSnd();
        int seguido = request.getThird();

        for (Pair<Integer> current : siguiendo.get(seguidor)) {
          if (current.estaSiguiendo() == seguido) {
            siguiendo.get(seguidor).remove(current);
            break;
          }
        }
        
        //aviso invocador que termino de procesar
        request.getChannel().out().write(null);
      }

      // procesar peticiones ENVIAR
      // con un if basta
      // for (RequestGritter<String, Boolean> request : enviarRequests) {
      if (!enviarRequests.isEmpty()) {
        // remuevo el item
        RequestGritter<String, Boolean> request = enviarRequests.poll();
        
        // siempre puedo procesar enviar
        // @assert true;
        int userid = (int) request.getChannel().in().read();
        String grito = request.getSecond();
        Boolean regrito = request.getThird();
        // primero busco los seguidores
        Set<Integer> seguidores = new HashSet<>();
        for (Entry<Integer, Set<Pair<Integer>>> seguidor : siguiendo.entrySet()) {
          for (Pair<Integer> current : seguidor.getValue()) {
            if (current.estaSiguiendo() == userid && ((regrito && current.leeRegritos()) || !regrito)) {
              seguidores.add(seguidor.getKey());
            }
          }
        }

        // ahora que tengo los seguidores, hago broadcast
        for (Integer seguidor : seguidores) {
          if (gritosPorLeer.get(seguidor) == null) { // creo contenedor de gritos
            gritosPorLeer.put(seguidor, new HashSet<String>());
          }
          gritosPorLeer.get(seguidor).add(grito);
        }
        
        //aviso invocador que termino de procesar
        request.getChannel().out().write(null);
      }

      // procesar peticiones LEER
      // aca si hace falta el bucle
      if (!leerRequests.isEmpty()) {
        LinkedList<Request<Integer>> requestsToRemove = new LinkedList<Request<Integer>>();
        for (Request<Integer> request : leerRequests) {
          int uid = request.getFootprint();
          
          if (gritosPorLeer.get(uid) != null && !gritosPorLeer.get(uid).isEmpty()) {
            // remuevo el item
            requestsToRemove.add(request);
            // @ assert this.gritosPorLeer.get(uid) != null && !this.gritosPorLeer.get(uid).isEmpty();
            
            // leo el mensaje que haya - no importa orden
            String grito = gritosPorLeer.get(uid).iterator().next();
            gritosPorLeer.get(uid).remove(grito);
            //aviso invocador que termino de procesar
            request.getChannel().out().write(grito);
          }
        }
        // removing processed requests
        leerRequests.removeAll(requestsToRemove);
      }
    }// end while server
  } // end run

}
