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
public class GestorGritterCSP implements CSProcess, GestorGritter {

  /**
   * Guarda quien sigue a quien
   */
  protected Map<Integer, Set<Pair<Integer>>> siguiendo;

  /**
   * Mensajes que aun no han sido escuchados por el usuario
   */
  protected Map<Integer, Set<String>> gritosPorLeer;

  /** WRAPPER IMPLEMENTATION */
  /**
   * canales para recibir las peticiones
   */
  Any2OneChannel chSeguir = Channel.any2one();
  Any2OneChannel chDejarDeSeguir = Channel.any2one();
  Any2OneChannel chEnviar = Channel.any2one();
  Any2OneChannel chLeer = Channel.any2one();

  /**
   * listas de peticiones aplazadas
   */
  private final Queue<RequestGritter<Integer, Integer>> seguirRequests = new LinkedList<>();
  private final Queue<RequestGritter<Integer, Integer>> dejarDeSeguirRequests = new LinkedList<>();
  private final Queue<RequestGritter<String, Boolean>> enviarRequests = new LinkedList<>();
  private final Queue<Request<Integer>> leerRequests = new LinkedList<>();

  public GestorGritterCSP() {
    siguiendo = new HashMap<>();
    gritosPorLeer = new HashMap<>();
  }

  @Override
  public void enviar(int uid, String grito, boolean regrito) {
    // PRE
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
    // PRE
    Pair<Integer> seguidorPair = null;
    for (Pair<Integer> current : this.siguiendo.get(seguidor)) {
      if (current.estaSiguiendo() == seguido) {
        seguidorPair = current;
        break;
      }
    }

    if (seguidorPair == null) {
      throw new PreViolationSharedResourceException();
    }

    One2OneChannel innerChannel = Channel.one2one();
    // enviar footprint de la invocacion junto con el canal auxiliar
    chDejarDeSeguir.out().write(new RequestGritter<Integer, Integer>(innerChannel, seguidor, seguido));
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
        // encolar la nueva peticion
        dejarDeSeguirRequests.add((RequestGritter<Integer, Integer>) chDejarDeSeguir.in().read());
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
        RequestGritter<Integer, Integer> request = seguirRequests.poll();
        // @ assert true;

        int seguidor = request.getSnd();
        int seguido = request.getThird();
        boolean regritos = (boolean) request.getChannel().in().read();

        // si aun no existe el usuario creo el set asociado y agrego el par
        if (!this.siguiendo.containsKey(seguidor)) {
          this.siguiendo.put(seguidor, new HashSet<Pair<Integer>>());
        }

        Pair<Integer> value = null;
        // ya existe el set de seguidores, cambio los regritos
        for (Pair<Integer> current : this.siguiendo.get(seguidor)) {
          if (current.estaSiguiendo() == seguido) {
            current.setRegrito(regritos);
            value = current;
            break;
          }
        }

        if (value == null) { // no estaba siguiendo
          // creo y agrego el par nuevo
          value = new Pair<Integer>(seguido, regritos);
          this.siguiendo.get(seguidor).add(value);
        }
      }

      // procesar peticiones DEJARDESEGUIR
      // no hace falta bucle
      if (!dejarDeSeguirRequests.isEmpty()) {
        RequestGritter<Integer, Integer> request = dejarDeSeguirRequests.poll();
        // @ assert true;

        int seguidor = request.getSnd();
        int seguido = request.getThird();

        for (Pair<Integer> current : this.siguiendo.get(seguidor)) {
          if (current.estaSiguiendo() == seguido) {
            this.siguiendo.get(seguidor).remove(current);
            break;
          }
        }
      }
      // boolean requestProcessed = true;
      // while (requestProcessed) {
      // requestProcessed = false;
      // procesar peticiones ENVIAR
      // con un if basta
      // for (RequestGritter<String, Boolean> request : enviarRequests) {
      if (!enviarRequests.isEmpty()) {
        RequestGritter<String, Boolean> request = enviarRequests.poll();
        // siempre puedo procesar enviar
        // @assert true;
        int userid = (int) request.getChannel().in().read();
        String grito = request.getSecond();
        Boolean regrito = request.getThird();
        // primero busco los seguidores
        Set<Integer> seguidores = new HashSet<>();
        for (Entry<Integer, Set<Pair<Integer>>> seguidor : this.siguiendo.entrySet()) {
          for (Pair<Integer> current : seguidor.getValue()) {
            if (current.estaSiguiendo() == userid && ((regrito && current.leeRegritos()) || !regrito)) {
              seguidores.add(seguidor.getKey());
            }
          }
        }

        // ahora que tengo los seguidores, hago broadcast
        for (Integer seguidor : seguidores) {
          if (gritosPorLeer.get(seguidor) == null) { // creo contenedor de
                                                     // gritos
            this.gritosPorLeer.put(seguidor, new HashSet<String>());
          }
          this.gritosPorLeer.get(seguidor).add(grito);
        }
      }

      // procesar peticiones LEER
      // aca si hace falta el bucle
      for (Request<Integer> request : leerRequests) {
        int uid = request.getFootprint();
        // @ assert this.gritosPorLeer.get(uid) != null &&
        // !this.gritosPorLeer.get(uid).isEmpty();
        if (this.gritosPorLeer.get(uid) != null && !this.gritosPorLeer.get(uid).isEmpty()) {
          // leo el mensaje que haya - no importa orden
          String grito = this.gritosPorLeer.get(uid).iterator().next();
          this.gritosPorLeer.get(uid).remove(grito);
        }
      }
    }
  } // end run

}
