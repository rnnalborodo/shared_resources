package es.upm.babel.ccjml.samples.gritter.java.runenv;

import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import es.upm.babel.ccjml.samples.gritter.java.GestorGritter;
import es.upm.babel.ccjml.samples.gritter.java.GestorGritterMonitorIndexClientes;

/**
 * Main class.
 * 
 * @author Babel Group
 */
public class Gritter {
  
  static String ingreso;
  // randomize utilizado para ejecutar el no determinismo
  static final java.util.Random rdm = 
                               new java.util.Random(System.currentTimeMillis());
  
  public static final void main(final String[] args) {

        final GestorGritter sharedResource = new GestorGritterMonitorIndexClientes();

        // usuarios ya creados
        List<Integer> usuariosCreados = new LinkedList<Integer>();

        // los usuarios son generados hasta que se presione alguna tecla
        new Thread(){
          public void run(){
            Scanner sc = new Scanner(System.in);
            Gritter.ingreso = null;
            System.out.println("Terminar la ejecucion - apretar tecla d");
            Gritter.ingreso = sc.nextLine();
            System.out.println("=========== terminada la generacion de usuarios");
            ingreso.trim();
          }
        }.start();

        // Declaracion de los usuarios del sistema
        int i = 0;
        while (ingreso == null){
          int uid = Math.abs(rdm.nextInt());

          // si ya existe, vuelvo al loop
          if (usuariosCreados.contains(uid)) {
            System.out.println("=========== ya creado");
            continue;
          }

          usuariosCreados.add(uid);

          new User(uid, sharedResource, usuariosCreados).start();
          // para probar sin los usuarios
          // System.out.println("genere a " + Math.abs(rdm.nextInt()));
        }
  } 
}