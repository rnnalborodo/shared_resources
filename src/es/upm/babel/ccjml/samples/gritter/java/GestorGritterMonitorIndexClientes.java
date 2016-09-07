package es.upm.babel.ccjml.samples.gritter.java;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import es.upm.babel.ccjml.samples.utils.PreViolationSharedResourceException;
import es.upm.babel.cclib.Monitor;

/**
 * Implementacion del Gestor Gritter usando monitores con prioridad 
 * correspondiente a la primera practica de Concurrencia de 2015-2016 
 * 
 * Usando indexacion por parametros
 * 
 * @version 0.1
 * @author Babel Group
 */
public class GestorGritterMonitorIndexClientes implements GestorGritter {

  /**
   * Guarda quien sigue a quien
   */
  protected Map<Integer,Set<Pair<Integer>>> siguiendo;
  
  /**
   * Mensajes que aun no han sido escuchados por el usuario
   */
  protected Map<Integer,Set<String>> gritosPorLeer;
  
  private final Monitor mutex;
  
  /**
   * Un usuario esta bloqueado sii no tiene mensajes por leer
   */
  private final Map<Integer,Monitor.Cond> usuariosEsperandoGritos;
    
  public GestorGritterMonitorIndexClientes(){
    
    siguiendo = new HashMap<>();
    gritosPorLeer = new HashMap<>();

    mutex = new Monitor();
    usuariosEsperandoGritos = new HashMap<>();
  }

  @Override
  public void seguir(int seguidor, int seguido, boolean regritos) 
                                    throws PreViolationSharedResourceException {
    if (seguidor == seguido){
      throw new PreViolationSharedResourceException();
    }
    mutex.enter(); 
    // CPRE true

    // actualizo el nuevo seguidor con sus regritos
    
    // si aun no existe el usuario creo el set asociado y agrego el par
    if (!this.siguiendo.containsKey(seguidor)){
      this.siguiendo.put(seguidor, new HashSet<Pair<Integer>>());
    } 

    Pair<Integer> value = null;
    // ya existe el set de seguidores, cambio los regritos
    for(Pair<Integer> current : this.siguiendo.get(seguidor)){
      if (current.estaSiguiendo() == seguido) {
        current.setRegrito(regritos);
        value = current;
        break;
      }
    }

    if (value == null){ // no estaba siguiendo 
      // creo y agrego el par nuevo
      value = new Pair<Integer>(seguido, regritos);      
      this.siguiendo.get(seguidor).add(value);
    }
    
    // desbloquear threads dormidos
    mutex.leave();
  }

  @Override
  public void dejarDeSeguir(int seguidor, int seguido) 
                                    throws PreViolationSharedResourceException {
    mutex.enter();
    // PRE - no esta siguiendo
    Pair<Integer> seguidorPair = null;
    for(Pair<Integer> current : this.siguiendo.get(seguidor)){
      if (current.estaSiguiendo() == seguido) {
        seguidorPair  = current;
        break;
      }
    }
    
    if(seguidorPair == null){
      mutex.leave();
      throw new PreViolationSharedResourceException();
    }
    
    // CPRE true

    // quito el seguidor
    
    this.siguiendo.get(seguidor).remove(seguidorPair);
    
    // desbloquear threads dormidos
    mutex.leave(); 
  }

  @Override
  public void enviar(int uid, String grito, boolean regrito) {
    // PRE true

    mutex.enter();
    
    // CPRE true
    
    // en base a todos los posibles usuarios que lo esten siguiendo
    // lo agrego a la lista particular de cada seguidor

    // primero busco los seguidores
    Set<Integer> seguidores = new HashSet<>();
    for(Entry<Integer,Set<Pair<Integer>>> seguidor :this.siguiendo.entrySet()) {
      for(Pair<Integer> current : seguidor.getValue()){
        if (current.estaSiguiendo() == uid
            &&
            ((regrito && current.leeRegritos()) || !regrito)
           ) {
          seguidores.add(seguidor.getKey());
        }
      }
    }
        
    // ahora que tengo los seguidores, hago broadcast
    for (Integer seguidor : seguidores) {
      if (gritosPorLeer.get(seguidor) == null) { // creo contenedor de gritos
        this.gritosPorLeer.put(seguidor, new HashSet<String>());
      }
      this.gritosPorLeer.get(seguidor).add(grito);
    }
    
    
    // desbloquear threads dormidos

    for (Integer seguidor : seguidores) {
      if (usuariosEsperandoGritos.containsKey(seguidor)) {
        this.usuariosEsperandoGritos.get(seguidor).signal();
        break;
      }
    }
        
    mutex.leave();
  }

  
  @Override
  public String leer(int uid) {
    // PRE true

    mutex.enter();
    // CPRE
    if ( this.gritosPorLeer.get(uid) == null 
         || this.gritosPorLeer.get(uid).isEmpty()) {
      Monitor.Cond cond = mutex.newCond();
      this.usuariosEsperandoGritos.put(uid, cond);
      cond.await();
    }
    
    // leo el mensaje que haya - no importa orden
    String grito = this.gritosPorLeer.get(uid).iterator().next();
    this.gritosPorLeer.get(uid).remove(grito);
    
    // desbloquear threads dormidos
    for (Integer seguidor : usuariosEsperandoGritos.keySet()) {
      if (gritosPorLeer.get(seguidor) != null && !gritosPorLeer.get(seguidor).isEmpty()) {
        Monitor.Cond cond = usuariosEsperandoGritos.get(seguidor);
        this.usuariosEsperandoGritos.remove(seguidor);
        cond.signal();
        break;
      }
    }

    mutex.leave();
    
    return grito;
  }
}