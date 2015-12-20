package es.upm.babel.ccjml.samples.warehouse.java;

import org.jcsp.lang.CSProcess;

/** 
 * WarehouseAccessControl implementation using JCSP.
 * 
 * @author Julio Mariño - BABEL Group - Technical University of Madrid
 */
public class WarehouseAccessControlCSP_allselect implements WarehouseAccessControl, CSProcess {

  public static final int N_ROBOTS = Robots.N_ROBOTS;
  public static final int N_WAREHOUSE = Robots.N_WAREHOUSE;
  public static final int MAX_WEIGHT_IN_WAREHOUSE = Robots.MAX_WEIGHT_IN_WAREHOUSE;
  
  
  @Override
  public void run() {
    // TODO Auto-generated method stub
    
  }
  @Override
  public void enterWarehouse(int n, int w) {
    // TODO Auto-generated method stub
    
  }
  @Override
  public void exitWarehouse(int n, int w) {
    // TODO Auto-generated method stub
    
  }
  
//  public WarehouseAccessControlCSP_allselect() {
//    // DECLARACION DE CANALES PARA COMUNICAR LAS OPERACIONES DEL
//    // RECURSO COMPARTIDO CON EL SERVIDOR
//    // un canal "sumidero" para robots masivos que quieren entrar
//    // en la nave 0:
//    Any2OneChannel lars_favourite_channel = Channel.any2one();
//    // tantos canales como pesos, para solicitarEntrar(0,p):
//    Any2OneChannel entrar0[] new Any2OneChannel[MAX_WEIGHT_IN_WAREHOUSE];
//    for (int p = 0; p < MAX_WEIGHT_IN_WAREHOUSE; p++) {
//      entrar0[p] = Channel.any2one();
//    } 
//    // tantos canales como naves (menos la 0) para comunicar el
//    // peso del robot que quiere entrar en la nave n (n > 0):
//    Any2OneChannel comunicarPeso[] = new Any2OneChannel[N_WAREHOUSE];
//    // tantos canales como naves (menos la 0) para pedir permiso
//    // para entrar en la nave n (n > 0):
//    Any2OneChannel permisoEntrar[] = new Any2OneChannel[N_WAREHOUSE];
//    // tantos canales como naves para pedir permiso para salir de
//    // una nave 
//    Any2OneChannel permisoSalir[] = new Any2OneChannel[N_WAREHOUSE];
//    // los creamos:
//    for (int n = 0; n < N_WAREHOUSE; n++) {
//      comunicarPeso[n] = Channel.any2one();
//      permisoEntrar[n] = Channel.any2one();
//      permisoSalir[n]  = Channel.any2one();
//    } 
//    // juntamos todos estos canales en un único vector:
//    AltingChannelInput[] = 
//        new AltingChannelInput[1 + 3*N_WAREHOUSE];
//  }
//
//  // METODOS PARA TRADUCIR PARAMETROS A CANALES DE PETICION
//  private 
//
//  // CODIGO DE LLAMADA A LAS _OPERACIONES_ DEL RECURSO COMPARTIDO QUE
//  // SE EJECUTA _EN_LOS_THREADS_CLIENTE_ !!
//  public void enterWarehouse(int n, int p) {
//    if (n == 0) { 
//      if (p > MAX_PESO_EN_NAVE) {
//        // nos protegemos contra los tests de Lars el malefico
//        servicios[robotGordo()].out().write(p);
//      } else { // nave 0, peso legal
//        // desglosamos por pesos
//        servicios[entrar0(p)].out().write(null);
//      }
//    } else { // resto de naves
//      // tenemos un canal por nave para enviar el peso
//      // actualizado y otro ya para pedir entrar (2ble bloqueo
//      // en forma send/send:
//      // actualizamos el peso del robot que esta en el pasillo n 
//      servicios[pesoPasillo(n)].out().write(p);
//      // pedimos permiso para pasar del pasillo n a la nave n 
//      // (n > 0)
//      servicios[permisoEntrar(n)].out().write(null);
//    }
//  }
//  public void exitWarehouse(int n, int p) {
//    // while (n < Robots.N_WAREHOUSE - 1 && ocupado[n+1]) {
//    //     try { this.wait(); } catch (Exception e) {};
//    // }
//    // peso[n] -= p;
//    // if (n < Robots.N_WAREHOUSE - 1) {
//    //     ocupado[n+1] = true;
//    // }
//    // this.notifyAll();
//  }
//
//  // CODIGO DEL _SERVIDOR_ EN EL METODO run() !!
//  public void run() {
//    // ESTADO DEL RECURSO COMPARTIDO AQUI
//    int peso[] = new int[Robots.N_WAREHOUSE];
//    boolean ocupado[] = new boolean[Robots.N_WAREHOUSE];
//
//    // ESTADO ADICIONAL PARA 2BLES BLOQUEOS, PETICIONES APLAZADAS,
//    // ETC
//    // Para guardar el peso del robot que esta en el pasillo, o 0
//    // si no hay robot. Necesario para completar
//    // solicitarEntrar(n,p) con dos envios cuando n > 0.
//    int pesoPasillo[] = new int[Robots.N_WAREHOUSE];
//
//    // DECLARACION DE ESTRUCTURAS PARA RECEPCION ALTERNATIVA
//
//    // VARIABLES AUXILIARES A LA RECEPCION ALTERNATIVA
//    // para guardar el indice del vector de servicios:
//    int cual;
//    // para traducir canales a pesos cuando se entra en la nave 0
//    int que_peso_0;
//    // para traducir canales a pasillos cuando se comunica el peso
//    // del robot en solicitarEntrar(n,p), si n > 0. 
//    int que_pasillo;
//    // para traducir canales a naves cuando se confirma la entrada
//    // del robot en solicitarEntrar(n,p), si n > 0.
//    int que_nave;
//    // para traducir canales a naves cuando se confirma la salida
//    // del robot en solicitarSalir(n,p), si n > 0.
//    // (reutilizamos que_nave)
//
//    // BUCLE PRINCIPAL DEL SERVIDOR
//    while (true) {
//      // REFRESCO DE LAS GUARDAS, _SIN_OPTIMIZAR_ !!
//      // robots masivos: nunca los aceptamos:
//      sincCond[pesoGordo()] == false;
//      // entrada de robots legales, nave 0:
//      for (int p = 0; p <= MAX_PESO_NAVE; p++) {
//        sincCond[entrar0(p)] = p <= peso[0];
//      }
//      // comunicar peso pasillo, n > 0:
//      for (int n = 0; n < MAX_NAVES; n++) {
//        sincCond[pesoPasillo(n)] = true;
//      } 
//      // solicitar entrar, n > 0:
//      for (int n = 1; n < MAX_NAVES; n++) {
//        sincCond[permisoEntrar(n)] = 
//            pesoPasillo(n) < MAX_PESO_NAVE - peso(n);
//      } 
//      // solicitar salir:
//      for (int n = 1; n < MAX_NAVES; n++) {
//        sincCond[permisoSalir(n)] =
//            n == MAX_NAVES-1 || !ocupado(n+1);
//      } 
//
//      // LA SELECT
//      cual = servicios.fairselect(sincCond);
//      // tratamiento de casos
//      // robot gordo
//      // no aceptamos robots gordos
//      // entrada de robots legales, nave 0:
//      if (esLegal0(cual)){
//        // el peso viene en el mensaje
//        peso[0] += (Integer)servicios[cual].read();
//      } else if (esPesoPasillo(cual)) {
//        que_pasillo = quePesoPasillo(cual);
//        pesoPasillo[que_pasillo] = 
//            (Integer)servicios[cual].read();
//      } else if (esLegalN(cual)) {
//        servicios[cual].read();
//        que_n_entra = queEntrarN(cual);
//        peso[que_n_entra] += pesoPasillo(que_n_entra);
//        ocupado[que_n_entra] = false;
//        pesoPasillo[que_n_entra] = 0;
//      } else if (esSalir(cual)) {
//        servicios[cual].read();
//        que_n_sale = queSalir(cual);
//        if (que_n_sale < MAX_NAVES-1) {
//          ocupado[que_n_sale] = true;
//        }
//      } else {
//        // lanzar una excepción
//      }
//    } // FIN BUCLE SERVIDOR
//  } // FIN SERVIDOR

}
