package es.upm.babel.ccjml.samples.gritter.java.test;

import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import org.junit.Test;

import es.upm.babel.ccjml.samples.gritter.java.GestorGritter;
import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;
import es.upm.babel.cclib.Tryer;

/**
 * @author raul.alborodo
 *
 */
public abstract class TestGritter {

  // solo para que sea practico
  final int MAX_ID = 4;

  // generador aleatorio unico
  final Random randomGenerator = new Random();

  // el recurso compartido
  protected GestorGritter resource = null;

  // traza rescatada hasta el momento
  protected String trace = null;

  // clases simulando las operaciones
  class SeguirTG extends Tryer {
    int seguidor;
    int seguido;
    boolean regritos;
    Exception exception;

    public SeguirTG(int seguidor, int seguido, boolean regritos) {
      this.seguido = seguido;
      this.seguidor = seguidor;
      this.regritos = regritos;
    }

    // retorno una cadena que representa la llamada al metodo
    private String call() {
      return "seguir(" + seguidor + ", " + seguido + ", " + regritos + ");";
    }

    // llamando al metodo del recurso compartido
    // actualizo la traza
    public void toTry() {
      exception = null;
      trace += call();
      try {
        resource.seguir(seguidor, seguido, regritos);
      } catch (PreViolationSharedResourceException _e) {
        exception = _e;
      }
    }

    public Throwable getException() {
      return exception;
    }

    public boolean lanzoException() {
      return exception != null;
    }
  }

  class DejarDeSeguirTG extends Tryer {
    int seguidor;
    int seguido;
    Exception exception;

    public DejarDeSeguirTG(int seguidor, int seguido) {
      this.seguido = seguido;
      this.seguidor = seguidor;
    }

    // retorno una cadena que representa la llamada al metodo
    private String call() {
      return "dejarDeSeguir(" + seguidor + ", " + seguido + ");";
    }

    // llamando al metodo del recurso compartido
    // actualizo la traza
    public void toTry() {
      exception = null;
      trace += call();
      try {
        resource.dejarDeSeguir(seguidor, seguido);
      } catch (Exception _e) {
        exception = _e;
      }
    }

    public Throwable getException() {
      return exception;
    }

    public boolean lanzoException() {
      return exception != null;
    }
  }

  class EnviarTG extends Tryer {
    int uid;
    String msg;
    boolean regrito;
    Throwable exception;

    public EnviarTG(int seguidor, String seguido, boolean regritos) {
      this.msg = seguido;
      this.uid = seguidor;
      this.regrito = regritos;
    }

    // retorno una cadena que representa la llamada al metodo
    private String call() {
      return "enviar(" + uid + ", " + msg + ", " + regrito + ");";
    }

    // llamando al metodo del recurso compartido
    // actualizo la traza
    public void toTry() {
      exception = null;
      trace += call();
      try {
        resource.enviar(uid, msg, regrito);
      } catch (Exception _e) {
        exception = _e;
      }
    }

    public Throwable getException() {
      return exception;
    }

    public boolean lanzoException() {
      return exception != null;
    }
  }

  class LeerTG extends Tryer {
    String msg;
    int seguidor;

    public LeerTG(int seguidor) {
      this.seguidor = seguidor;
    }

    // retorno una cadena que representa la llamada al metodo
    private String call() {
      return "leer(" + seguidor + ");";
    }

    // llamando al metodo del recurso compartido
    // actualizo la traza
    public void toTry() {
      trace += call();
      msg = resource.leer(seguidor);
    }

    public String msg() {
      return msg;
    }
  }

  // una constante para que haya esperas a las respuestas/procesos
  final protected int DELAY_MIN_MS = 300;

  /**
   * metodo que hace seguir desde 'Init' hasta 'max' con paso 'step' a seguido
   */
  private void /* @helper@ */ seguirUpToMAX(int init, int max, int step,
      int seguido, boolean regrito) {
    SeguirTG seguir[] = new SeguirTG[max];
    for (int i = init; i < max; i += step) {
      // no sigue a si mismo
      if (i == seguido)
        continue;

      seguir[i] = new SeguirTG(i, seguido, regrito);
      seguir[i].start();
      seguir[i].gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + seguir[i].call() + " shouldn't have blocked",
          !seguir[i].isBlocked());
    }
  }

  /**
   * metodo que hace seguir desde 'Init' hasta 'max' con paso 'step' a seguido
   */
  private void /* @helper@ */ seguirTodos(int init, int maxSeguidor,
      int maxSeguidos, int step, boolean regrito) {
    for (int i = init; i < maxSeguidor; i += step) {
      this.seguirUpToMAX(init, maxSeguidos, step, i, regrito);
    }
  }

  /**
   * Se puede hacer seguir de todos los usuarios que quiera siempre y cuando no
   * intente seguirme a mi mismo.
   */
  @Test
  public void seguirIlimitadoATerceros() {
    /* pid, eid */
    int seguido = randomGenerator.nextInt(MAX_ID);
    boolean regritos;

    for (int i = 0; i < MAX_ID; i++) {
      regritos = randomGenerator.nextBoolean();
      SeguirTG seguir = new SeguirTG(seguido, i, regritos);
      seguir.start();
      seguir.gimmeTime(DELAY_MIN_MS);

      // no se deberia bloquear el proceso aun con excepcion
      assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
          !seguir.isBlocked());

      if (i == seguido) { // si intento a seguir al mismo, hay excepcion
        assertTrue(
            trace + "-> " + seguir.call() + " should have thrown an exception",
            seguir.lanzoException());
      } else { // sino sigo normalmente
        assertTrue(
            trace + "-> " + seguir.call()
                + " shouldn't have thrown an exception",
            !seguir.lanzoException());
      }
    }
  }

  /**
   * Seguir varias veces al mismo, no viola el invariante
   */
  @Test
  public void seguirIlimitadoAUno() {
    // cualquiera mientras que sean distintos
    int seguido = 0;
    int seguidor = 1;
    boolean regritos;

    for (int i = 0; i < 20; i++) {
      regritos = randomGenerator.nextBoolean();
      SeguirTG seguir = new SeguirTG(seguido, seguidor, regritos);
      seguir.start();
      seguir.gimmeTime(DELAY_MIN_MS);

      // la llamada no deberia bloquearse ni lanzar excepcion
      assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
          !seguir.isBlocked());
      assertTrue(
          trace + "-> " + seguir.call() + " shouldn't have thrown an exception",
          !seguir.lanzoException());

    }
  }

  /**
   * dejarDeSeguir puede lanzar excepcion si antes no se esta siguiendo
   * 
   * primero se hace un seguir(X,Y,r) (puede lanzar excepcion - X == Y) segundo
   * se hace un dejarDeSeguir(X,Y) (puede lanzar excepcion - X == Y) tercero se
   * hace un dejarDeSeguir(X,Y) ( lanza excepcion si o si)
   */
  @Test
  public void dejarDeSeguirGeneraExcepcion() {
    // usando constantes para el caso de index por parametro
    int seguido = randomGenerator.nextInt(MAX_ID);
    int seguidor = randomGenerator.nextInt(MAX_ID);
    boolean regritos = randomGenerator.nextBoolean();

    // primero sigo al usuario
    SeguirTG seguir = new SeguirTG(seguidor, seguido, regritos);
    seguir.start();
    seguir.gimmeTime(DELAY_MIN_MS);

    // el proceso no deberia bloquearse
    assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
        !seguir.isBlocked());

    // luego dejo de seguirlo
    DejarDeSeguirTG dejarDeSeguir = new DejarDeSeguirTG(seguidor, seguido);
    dejarDeSeguir.start();
    dejarDeSeguir.gimmeTime(DELAY_MIN_MS);

    assertTrue(trace + "-> " + dejarDeSeguir.call() + "shouldn't have blocked",
        !dejarDeSeguir.isBlocked());

    if (seguido == seguidor) { // si ambos ID son iguales, lanzo EX
      // seguir deberia largar excepcion
      assertTrue(
          trace + "-> " + seguir.call() + " should have thrown an exception",
          seguir.lanzoException());

      // dejarDeSeguir tambien deberia largar excepcion
      assertTrue(
          trace + "-> " + dejarDeSeguir.call()
              + " should have thrown an exception",
          dejarDeSeguir.lanzoException());

    } else { // seguidor != seguido
      // seguir no deberia largar excepcion
      assertTrue(
          trace + "-> " + seguir.call() + " shouldn't have thrown an exception",
          !seguir.lanzoException());

      // dejarDeSeguir no deberia largar excepcion
      assertTrue(
          trace + "-> " + dejarDeSeguir.call()
              + " shouldn't have thrown an exception",
          !dejarDeSeguir.lanzoException());

      // intento deseguir al usuario nuevamente
      // deberia largar una excepcion sin bloquearse
      dejarDeSeguir = new DejarDeSeguirTG(seguidor, seguido);
      dejarDeSeguir.start();
      dejarDeSeguir.gimmeTime(DELAY_MIN_MS);

      assertTrue(
          trace + "-> " + dejarDeSeguir.call()
              + " (2nd call) shouldn't have blocked",
          !dejarDeSeguir.isBlocked());

      assertTrue(
          trace + "-> " + dejarDeSeguir.call()
              + "(2nd call) should have thrown an exception",
          dejarDeSeguir.lanzoException());
    }

  }

  /**
   * un usuario puede enviar todos los mensajes que quiere incluso mensajes
   * iguales
   */
  @Test
  public void enviarTodosLosQueQuiera() {
    /* pid, eid */
    int uid = randomGenerator.nextInt(MAX_ID);

    for (int i = 0; i < 20; i++) {
      boolean regrito = randomGenerator.nextBoolean();
      EnviarTG enviar = new EnviarTG(uid, String.valueOf(uid + " -> " + i),
          regrito);
      enviar.start();
      enviar.gimmeTime(DELAY_MIN_MS);

      assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
          !enviar.isBlocked());
    }
  }

  /**
   * la operacion leer bloquea al proceso hasta que otro envie un grito
   * distingue si es regrito o no
   */
  @Test
  public void leerBloqueaYEnviarDespierta() {
    // si o si distintos
    int usrSeguidor = 0;
    int usrSeguido = 1;

    // usrSeguidor sigue a usrSeguido sin regrito
    SeguirTG seguir = new SeguirTG(usrSeguidor, usrSeguido, false);
    seguir.start();
    seguir.gimmeTime(DELAY_MIN_MS);

    // no deberia ni bloquearse ni lanzar excepcion
    assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
        !seguir.isBlocked());
    assertTrue(
        trace + "-> " + seguir.call() + " shouldn't have thrown an exception",
        !seguir.lanzoException());

    // el seguidor intenta leer y debe quedarse bloqueado
    LeerTG leer = new LeerTG(usrSeguidor);
    leer.start();
    leer.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + leer.call() + " should have blocked",
        leer.isBlocked());

    // usrSeguido envia un regrito - no despierta a usrSeguidor
    EnviarTG enviar = new EnviarTG(usrSeguido, "shall not wake up", true);
    enviar.start();
    enviar.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
        !enviar.isBlocked());
    assertTrue(trace + "-> " + leer.call() + " shouldn't unblocked",
        leer.isBlocked());

    // usrSeguido envia un regrito para despierta a usrSeguidor
    enviar = new EnviarTG(usrSeguido, "shall wake up", false);
    enviar.start();
    enviar.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
        !enviar.isBlocked());
    assertTrue(trace + "-> " + leer.call() + " should unblocked",
        !leer.isBlocked());
  }

  /**
   * la operacion leer, lee gritos aunque seguir sea con regrito
   */
  @Test
  public void sigueConRegritoYDespiertaConGritoNormal() {
    // si o si distintos
    int usrSeguidor = 0;
    int usrSeguido = 1;

    // usrSeguidor sigue a usrSeguido sin regrito
    SeguirTG seguir = new SeguirTG(usrSeguidor, usrSeguido, true);
    seguir.start();
    seguir.gimmeTime(DELAY_MIN_MS);

    // no deberia ni bloquearse ni lanzar excepcion
    assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
        !seguir.isBlocked());
    assertTrue(
        trace + "-> " + seguir.call() + " shouldn't have thrown an exception",
        !seguir.lanzoException());

    // el seguidor intenta leer y debe quedarse bloqueado
    LeerTG leer = new LeerTG(usrSeguidor);
    leer.start();
    leer.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + leer.call() + " should have blocked",
        leer.isBlocked());

    // usrSeguido envia un grito normal - despierta a usrSeguidor
    EnviarTG enviar = new EnviarTG(usrSeguido, "shall not wake up", false);
    enviar.start();
    enviar.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
        !enviar.isBlocked());
    assertTrue(trace + "-> " + leer.call() + " should unblocked",
        !leer.isBlocked());
  }

  /**
   * leer, lee regritos sii se sigue al usuario con regritos
   */
  @Test
  public void sigueConRegritoYDespiertaConRegrito() {
    // si o si distintos
    int usrSeguidor = 0;
    int usrSeguido = 1;

    // usrSeguidor sigue a usrSeguido sin regrito
    SeguirTG seguir = new SeguirTG(usrSeguidor, usrSeguido, true);
    seguir.start();
    seguir.gimmeTime(DELAY_MIN_MS);

    // no deberia ni bloquearse ni lanzar excepcion
    assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
        !seguir.isBlocked());
    assertTrue(
        trace + "-> " + seguir.call() + " shouldn't have thrown an exception",
        !seguir.lanzoException());

    // el seguidor intenta leer y debe quedarse bloqueado
    LeerTG leer = new LeerTG(usrSeguidor);
    leer.start();
    leer.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + leer.call() + " should have blocked",
        leer.isBlocked());

    // usrSeguido envia un regrito - despierta a usrSeguidor
    EnviarTG enviar = new EnviarTG(usrSeguido, "shall not wake up", true);
    enviar.start();
    enviar.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
        !enviar.isBlocked());
    assertTrue(trace + "-> " + leer.call() + " should unblocked",
        !leer.isBlocked());
  }

  /**
   * enviar guarda solo una copia del mensaje si este ya existe Ver sets en la
   * especificacion
   */
  @Test
  public void enviarDosMensajesPuedeSerUno() {
    // si o si distintos
    int usrSeguidor = 0;
    int usrSeguido = 1;

    // usrSeguidor sigue a usrSeguido sin regrito
    SeguirTG seguir = new SeguirTG(usrSeguidor, usrSeguido, true);
    seguir.start();
    seguir.gimmeTime(DELAY_MIN_MS);

    // no deberia ni bloquearse ni lanzar excepcion
    assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
        !seguir.isBlocked());
    assertTrue(
        trace + "-> " + seguir.call() + " shouldn't have thrown an exception",
        !seguir.lanzoException());

    String str = "shall be the same";
    // usrSeguido envia un regrito normal
    EnviarTG enviar = new EnviarTG(usrSeguido, str, true);
    enviar.start();
    enviar.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
        !enviar.isBlocked());

    // usrSeguido envia un grito normal con el mismo mensaje
    // no debe ser guardado al existir un mensaje igual
    enviar = new EnviarTG(usrSeguido, str, false);
    enviar.start();
    enviar.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
        !enviar.isBlocked());

    // el seguidor lee el primer mensaje
    LeerTG leer = new LeerTG(usrSeguidor);
    leer.start();
    leer.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + leer.call() + " shouldn't have blocked",
        !leer.isBlocked());

    // el seguidor lee el segundo mensaje pero no deberia existir
    leer = new LeerTG(usrSeguidor);
    leer.start();
    leer.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + leer.call() + " should have blocked",
        leer.isBlocked());
  }

  // traza de Salva
  // INFO: 0 ahora sigue a 1 sin regritos
  // de maig 04, 2016 4:01:14 PM User run
  // INFO: 1 ahora sigue a 0 con regritos
  // de maig 04, 2016 4:01:14 PM User run
  // INFO: 0 grito -> Mensaje 8 creado por 0 no es regrito.
  // de maig 04, 2016 4:01:14 PM User run
  // INFO: 1 grito -> Mensaje 8 creado por 1 es regrito.
  // ....
  // INFO: 1 lee -> Mensaje 8 creado por 0
  // de maig 04, 2016 4:01:14 PM User run
  // INFO: 0 lee -> Mensaje 8 creado por 1
  // de maig 04, 2016 4:01:14 PM User run
  @Test
  public void leerCorrectos() {

    SeguirTG seguir = new SeguirTG(0, 1, false);
    seguir.start();
    seguir.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
        !seguir.isBlocked());

    seguir = new SeguirTG(1, 0, true);
    seguir.start();
    seguir.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + seguir.call() + " shouldn't have blocked",
        !seguir.isBlocked());

    EnviarTG enviar = new EnviarTG(0, "Mensaje de 0 SIN regrito! ", false);
    enviar.start();
    enviar.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
        !enviar.isBlocked());

    enviar = new EnviarTG(1, "Mensaje de 1 CON regrito!", true);
    enviar.start();
    enviar.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
        !enviar.isBlocked());

    LeerTG leer = new LeerTG(1);
    leer.start();
    leer.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + leer.call() + " shouldn't have blocked",
        !leer.isBlocked());

    leer = new LeerTG(0);
    leer.start();
    leer.gimmeTime(DELAY_MIN_MS);
    assertTrue(trace + "-> " + leer.call() + " should keep block",
        leer.isBlocked());

  }

  /**
   * Enviar despierta a todos sus seguidores que esten dormidos
   */
  @Test
  public void enviarDepiertaATodos() {

    int seguido = 2;
    seguirUpToMAX(0, MAX_ID, 1, seguido, false);

    LeerTG leer[] = new LeerTG[MAX_ID];

    for (int i = 0; i < leer.length; i++) {
      // no sigue a si mismo
      if (i == seguido)
        continue;

      leer[i] = new LeerTG(i);
      leer[i].start();
      leer[i].gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + leer[i].call() + " should have blocked",
          leer[i].isBlocked());
    }
    EnviarTG enviar = null;
    try {

      enviar = new EnviarTG(seguido, "Mensaje de 2 SIN regrito! ", false);
      enviar.start();
      enviar.gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
          !enviar.isBlocked());

      for (int i = 0; i < leer.length; i++) {
        if (i == seguido)
          continue;
        assertTrue(trace + "-> " + leer[i].call() + " should have unblocked",
            !leer[i].isBlocked());
      }
    } catch (java.lang.Error e) {
      assertTrue(e.getMessage(), false);
    }
  }

  /**
   * Leer lee un mensaje efectivamente enviado
   */
  @Test
  public void leerLeeCorrecto() {

    this.seguirTodos(0, MAX_ID, MAX_ID, 1, true);
    Set<String> mensajes = new HashSet<String>();

    // solo algunos envian pero despierta a todos pq se siguen todos
    for (int i = 0; i < MAX_ID; i += MAX_ID / 3) {
      String msg = "Mensaje de " + i + " SIN regrito! ";
      mensajes.add(msg);
      EnviarTG enviar = new EnviarTG(i, msg, false);
      enviar.start();
      enviar.gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + enviar.call() + " shouldn't have blocked",
          !enviar.isBlocked());
    }

    for (int i = 0; i < MAX_ID; i++) {
      LeerTG leer = new LeerTG(i);
      leer.start();
      leer.gimmeTime(DELAY_MIN_MS);
      assertTrue(trace + "-> " + leer.call() + " shouldn't have blocked",
          !leer.isBlocked());
      assertTrue(
          trace + "-> " + leer.call() + " should have read a sent message",
          mensajes.contains(leer.msg));
    }
  }

}
