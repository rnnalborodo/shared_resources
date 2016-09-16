package es.upm.babel.ccjml.samples.gritter.java.runenv;

import java.util.List;

import es.upm.babel.ccjml.samples.gritter.java.GestorGritter;
import es.upm.babel.cclib.ConcIO;

public class UserL extends Thread {
  
  // nro total de operaciones del recurso para generar el no determinismo
  private final int N_OPERATIONS = 4;
  // randomize utilizado para ejecutar el no determinismo
  private final java.util.Random rdm = 
                               new java.util.Random(System.currentTimeMillis());
  // contador usado para hacer trackeo de los mensajes enviados
  private int msgCounter = 0;

    // contador usado para hacer trackeo de los mensajes enviados
  private int noReadOperations = 0;
  private final int MIN_NO_READ_OPERATIONS = 2;

  // referencia al recurso compartido
  private final GestorGritter gestor;
  // ID del usuario
  private final int uid;

  private List<Integer> usuariosCreados;

  public UserL(int uid, GestorGritter ge, List<Integer> usrs ) {
    this.gestor = ge;
    this.uid = uid;
    this.usuariosCreados = usrs;
  }

  public void run() {
    while (true) {
      // nos dormimos un rato para no saturar el sistema
      // y para emular mejor el comportamiento real
//       try {
//         Thread.sleep(300 * (rdm.nextInt(5)+1));
//       } catch (InterruptedException e) {
//         ConcIO.printfnl("================= Oops, no se pudo dormir!" + e);
//       }

      // decidimos que operacion se va a ejecutar usando random
      int operation = Math.abs(rdm.nextInt()%N_OPERATIONS);
      
      switch (operation) {
        case 0: // operacion grito
          // creamos el mensaje usando StringBuffer para optimizar
          StringBuffer str = new StringBuffer()
              .append("Mensaje ").append(++msgCounter)
              .append(" creado por ").append(uid);
          
          // ejecutamos e imprimimos en el log
          ConcIO.printfnl("INIT:: enviar -> " + str.toString());
          boolean rg = rdm.nextBoolean();
          gestor.enviar(uid, str.toString(), rg);
          ConcIO.printfnl("END:: "+uid + " grito -> " + str +" --> regrito : "+rg);
          this.noReadOperations++;
          break;
  
        case 1: // follow
          // definimos si vamos a querer regritos o no de un usuario
          // generado aleatoriamente
          boolean regrito = rdm.nextBoolean();
          int followed = usuariosCreados.get
            (Math.abs(rdm.nextInt()% usuariosCreados.size()));
          
          // ejecutamos e imprimimos en el log
        try {
          ConcIO.printfnl("INIT:: seguir");
          gestor.seguir(this.uid,followed, regrito);
          ConcIO.printfnl("END:: "+this.uid + " ahora sigue a " + 
              followed + ((regrito)?" con":" sin") + " regritos");
          this.noReadOperations++;
        } catch (Exception e1) {
          ConcIO.printfnl("================= Oops, violo la precondicion! seguir("+
                         uid + "," + followed + ","+ regrito + ") : ");
        }
        
          break;
  
        case 2: // unfollow 
          try {
            followed = usuariosCreados.get
              (Math.abs(rdm.nextInt()% usuariosCreados.size()));
            
            // ejecutamos e imprimimos en el log
            // puede que no podamos hacer unfollow
            // Optimizacion: utilizar un set para saber a que 
            // usuarios estamos siguiendo
            ConcIO.printfnl("INIT:: DejarDeSeguir");
            gestor.dejarDeSeguir(this.uid, followed);
            ConcIO.printfnl("END:: "+this.uid + " deja de seguir a " + followed);
            this.noReadOperations++;
            
          } catch (Exception e) {
            ConcIO.printfnl("================= Oops, violo la precondicion de DEJAR DE SEGUIR!" );
          }
    
          break;
  
        case 3: // leer
          if (this.noReadOperations > MIN_NO_READ_OPERATIONS)
          //ejecutamos e imprimimos el/los mensajes leidos en el log
          {
            ConcIO.printfnl("INIT:: "+this.uid + " leyendo... " );
            String grito = gestor.leer(this.uid);
            ConcIO.printfnl("END:: "+this.uid + " lee -> " + grito);
            this.noReadOperations = 0;
          }
//          ConcIO.printfnl(this.uid + " too early " + this.noReadOperations);
          break;
      }
      
    }
  }
}
