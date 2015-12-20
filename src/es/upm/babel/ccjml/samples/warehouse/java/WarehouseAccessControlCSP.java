package es.upm.babel.ccjml.samples.warehouse.java;

/** 
 * WarehouseAccessControl implementation using JCSP
 * 
 * @author Julio Mariño - BABEL Group - Technical University of Madrid
 */

import java.util.PriorityQueue;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.AltingChannelInput;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.One2OneChannel;

public class WarehouseAccessControlCSP  implements WarehouseAccessControl, CSProcess {

  public static final int N_ROBOTS = Robots.N_ROBOTS;
  public static final int N_WAREHOUSE = Robots.N_WAREHOUSE;
  public static final int MAX_WEIGHT_IN_WAREHOUSE = Robots.MAX_WEIGHT_IN_WAREHOUSE;

  // DECLARACION DE CANALES PARA COMUNICAR LAS OPERACIONES DEL
  // RECURSO COMPARTIDO CON EL SERVIDOR
  // Solución mixta: uno para solicitarEntrar
  private Any2OneChannel cPetEntrar; 
  // por el que se envian objetos PetEntrar (ver mas abajo),
  // ...y tantos como naves para solicitarSalir:
  private Any2OneChannel[] cPetSalir;

  public WarehouseAccessControlCSP() {
    // construimos los canales
    cPetEntrar = Channel.any2one();
    cPetSalir = new Any2OneChannel[N_WAREHOUSE];
    for (int n = 0; n < N_WAREHOUSE; n++) {
      cPetSalir[n] = Channel.any2one();
    }
  }

  // CLASES INTERNAS PARA PETICIONES
  private class PetEntrar implements Comparable<Object> {
    public int nave;
    public int peso;
    public One2OneChannel cresp;

    PetEntrar(int n, int p) {
      this.nave = n;
      this.peso = p;
      this.cresp = Channel.one2one();
    }

    //@Override
    public int compareTo(Object otra) {
      return this.peso - ((PetEntrar)otra).peso;
    }
  }

  // CODIGO DE LLAMADA A LAS _OPERACIONES_ DEL RECURSO COMPARTIDO QUE
  // SE EJECUTA _EN_LOS_THREADS_CLIENTE_ !!
  public void enterWarehouse(int n, int p) {
    // creamos una peticion de entrar:
    PetEntrar pet = new PetEntrar(n,p);
    // la enviamos al servidor
    cPetEntrar.out().write(pet);
    // y esperamos una confirmación
    pet.cresp.in().read();
  }
  
  public void exitWarehouse(int n, int p) {
    // enviamos el peso por cPetSalir[n]
    cPetSalir[n].out().write(p);
    // esto bloquea hasta que el pasillo n+1 (si existe) está libre
  }

  // CODIGO DEL _SERVIDOR_ EN EL METODO run() !!
  public void run() {
    // ESTADO DEL RECURSO COMPARTIDO AQUI
    int peso[] = new int[N_WAREHOUSE];
    boolean ocupado[] = new boolean[N_WAREHOUSE];

    // ESTADO ADICIONAL PARA PETICIONES APLAZADAS, ETC.
    // Peticiones de entrar a la nave 0:
    PriorityQueue<PetEntrar> entrar0 = new PriorityQueue<PetEntrar>();
    // Para guardar las peticiones de entrar en una nave que no es
    // la 0 basta con una por pasillo:
    PetEntrar[] entrarN = new PetEntrar[N_WAREHOUSE];

    // DECLARACION DE ESTRUCTURAS PARA RECEPCION ALTERNATIVA
    AltingChannelInput[] inputs = new AltingChannelInput[N_WAREHOUSE+1];
    // las N_WAREHOUSE primeras entradas en alternativa serán las
    // peticiones de salir:
    for (int n = 0; n < N_WAREHOUSE; n++) {
      inputs[n] = cPetSalir[n].in();
    }
    // la última entrada es para las peticiones de entrar:
    inputs[N_WAREHOUSE] = cPetEntrar.in();
    // creamos la recepción alternativa:
    Alternative servicios = new Alternative(inputs);
    // creamos el vector de booleanos para la recepción
    // condicional: 
    boolean[] sincCond = new boolean[N_WAREHOUSE+1];
    // inicialmente se puede enviar cualquier peticion,
    // tanto de entrar...
    sincCond[N_WAREHOUSE] = true;
    // ...como de salir:
    for (int n = 0; n < N_WAREHOUSE; n++) {
      sincCond[n] = true; // == !ocupado[n+1]
    }

    // VARIABLES AUXILIARES A LA RECEPCION ALTERNATIVA
    // para guardar el indice del vector de servicios:
    int cual;

    // BUCLE PRINCIPAL DEL SERVIDOR
    while (true) {
      // LA SELECT
      cual = servicios.fairSelect(sincCond);
      // tratamiento de casos...
      // peticiones de entrar:
      if (cual == N_WAREHOUSE){
        // leemos la peticion:
        PetEntrar pet;
        pet = (PetEntrar)inputs[cual].read();
        // miramos si es para la nave 0:
        if (pet.nave == 0) {
          entrar0.add(pet);
        } else {
          entrarN[pet.nave] = pet;
        }
      } else { // es peticion de salir...
        // leemos la peticion y el canal nos proporciona el
        // numero de nave:
        int que_peso = (Integer)inputs[cual].read();
        int que_nave = cual;
        // si el mensaje se ha aceptado, es porque se puede
        // salir...
        if (que_nave < N_WAREHOUSE - 1) {
          ocupado[que_nave + 1] = true;
          // actualizamos la condicion de recepcion
          sincCond[que_nave] = false;
        }
        // actualizamos el peso de la nave
        peso[que_nave] -= que_peso;
      }
      // TRATAMIENTO DE PETICIONES APLAZADAS
      // solo se aplazan las peticiones de entrar
      // nave 0:
      while (entrar0.size() > 0 && 
          entrar0.peek().peso + peso[0] <= MAX_WEIGHT_IN_WAREHOUSE) {
        // sacamos petición de la cola
        PetEntrar pet = entrar0.poll();
        // incrementamos el peso de la nave
        peso[0] += pet.peso;
        // desbloqueamos al thread robot:
        pet.cresp.out().write(null);
      }
      // resto de naves, a razón de una peticion por nave:
      for (int n = 1; n < N_WAREHOUSE; n++) {
        if (ocupado[n] && entrarN[n] != null) { 
          // hay robot en pasillo n y quiere entrar en nave n
          if (entrarN[n].peso + peso[n] <= MAX_WEIGHT_IN_WAREHOUSE) {
            // incrementamos el peso de la nave
            peso[n] += entrarN[n].peso;
            // liberamos el pasillo
            ocupado[n] = false;
            // actualizamos la condicion de recepcion para
            // los que quieran _salir_ de la nave anterior:
            sincCond[n-1] = true;
            // desbloqueamos al thread robot:
            entrarN[n].cresp.out().write(null);
            // por seguridad, "vaciamos" el pasillo:
            entrarN[n] = null;
          }
        }   
      }
    } // FIN BUCLE SERVIDOR
  } // FIN SERVIDOR

}
