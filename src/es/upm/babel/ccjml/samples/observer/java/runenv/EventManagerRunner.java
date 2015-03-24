package es.upm.babel.ccjml.samples.observer.java.runenv;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.jcsp.lang.ProcessManager;

import es.upm.babel.ccjml.samples.observer.java.EventManager;
import es.upm.babel.ccjml.samples.observer.java.EventManagerCSP;
import es.upm.babel.ccjml.samples.observer.java.EventManagerMonitor;
import es.upm.babel.ccjml.samples.observer.java.EventManagerSync;
import es.upm.babel.ccjml.samples.utils.Utils;

/** Observer Main class. 
 * 
 * @author Babel Group
 */ 
public class EventManagerRunner {
  
  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());

  static final int N_EVENTS = 5;
  static final int N_PROCESSES = 11;

  public static final void main(final String[] args) {
   
    //cheking arguments
    Utils.ImplementationType implementation;
    
    if (args.length != 2 ){
      Logger.getLogger(EventManagerRunner.class.getName()).log(Level.SEVERE, "USAGE: {0} <implementation> <buffer_size>\n"
                      + "implementation = sync | mon | jcsp | default\n"
                      + "Using synchronization methods implementation", EventManagerRunner.class.getName());
      implementation = Utils.ImplementationType.SYNCHRONIZED;
      //System.exit(-1);
    } else {
      // ARG 0 -> Represents the chosen implementation to test
      switch (args[0]) {
        case "jcsp":
        case "2":
          implementation = Utils.ImplementationType.JCSP;
          break;
        case "mon":
        case "1":
          implementation = Utils.ImplementationType.MONITOR;
          break;
        case"sync":
        case"0": 
        default:
          implementation = Utils.ImplementationType.SYNCHRONIZED;
      }

    }
      
    // setting numbers of consumers and producers
    final int N_EMISORS = 2;
    final int N_OBSERVERS = 10;

    // Shared resource. Implementation selected based on input
    final EventManager sharedResource;
    switch (implementation){
      case SYNCHRONIZED:
        sharedResource = new EventManagerSync(N_EVENTS, N_PROCESSES);
        break;
      case MONITOR:
        sharedResource = new EventManagerMonitor(N_EVENTS, N_PROCESSES);
        break;
      case JCSP:
      default:
        EventManagerCSP buffer = new EventManagerCSP(N_EVENTS, N_PROCESSES);
        sharedResource = buffer;
        ProcessManager pm = new ProcessManager(buffer);
        pm.start();
    }

    // Declaration and creation of producers threads
    EventEmisor[] generators;
    generators = new EventEmisor[N_EMISORS];
    for (int i = 0; i < N_EMISORS; i++) {
      generators[i] = new EventEmisor(sharedResource, (random.nextInt(100) + 1)% N_EVENTS);
    }

    // Declaration and creation of consumers threads
    Observer[] observers;
    observers = new Observer[N_OBSERVERS];
    for (int i = 0; i < N_OBSERVERS; i++) {
      observers[i] = new Observer(sharedResource, i);
    }

    // Starting Threads
    for (int i = 0; i < N_EMISORS; i++) {
      generators[i].start();
    }
    
    for (int i = 0; i < N_OBSERVERS; i++) {
      observers[i].start();
    }
    
    // Wait until processes end
    // really necesary 'cause never ends! 
    try {
      for (int i = 0; i < N_EMISORS; i++) {
        generators[i].join();
      }
      for (int i = 0; i < N_OBSERVERS; i++) {
        observers[i].join();
      }
    } catch (InterruptedException ex) {
      Logger.getLogger(EventManagerRunner.class.getName()).log(
              Level.SEVERE, 
              ex.getMessage(),
              ex);

      System.exit (-1);
    }
  }
         
}
