package es.upm.babel.ccjml.samples.multibuffer.java.runenv;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.jcsp.lang.ProcessManager;

import es.upm.babel.ccjml.samples.multibuffer.java.Multibuffer;
import es.upm.babel.ccjml.samples.multibuffer.java.MultibufferCSPDeferredRequest;
import es.upm.babel.ccjml.samples.multibuffer.java.MultibufferMonitor;
import es.upm.babel.ccjml.samples.multibuffer.java.MultibufferSync;
import es.upm.babel.ccjml.samples.utils.Utils;

/**
 * Main class for <em>Multibuffer</em> problem. This class generates consumers and 
 * producers to execute and test the shared resource implementation
 * @author rnnalborodo
 */
public class MultibufferRunner {
  
  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());
  
  public static final void main(final String[] args) {
   
    //cheking arguments
    Utils.ImplementationType implementation;
    int bufferSize;
    
    if (args.length != 2 ){
      Logger.getLogger(MultibufferRunner.class.getName()).log(Level.SEVERE, "USAGE: {0} <implementation> <buffer_size>\n"
                      + "implementation = sync | mon | jcsp | default\n"
                      + "Using synchronization methods implementation and buffer size \"10\"", MultibufferRunner.class.getName());
      implementation = Utils.ImplementationType.SYNCHRONIZED;
      bufferSize = 3;
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

      //ARGS [1] buffer capacity
      try {
        bufferSize = Integer.parseInt(args[1]);
      } catch (NumberFormatException |  java.lang.ArrayIndexOutOfBoundsException ex) {
         Logger.getLogger(MultibufferRunner.class.getName()).log(
                Level.SEVERE, 
                "Wrong invocation. 10 as buffer size will be used");
        bufferSize = 3;
      }
    }
      
    // setting numbers of consumers and producers
    final int N_PRODS = 6;
    final int N_CONSS = 1;

    // Shared resource. Implementation selected based on input
    final Multibuffer sharedResource;
    switch (implementation){
      case SYNCHRONIZED:
        sharedResource = new MultibufferSync(bufferSize);
        break;
      case MONITOR:
        sharedResource = new MultibufferMonitor(bufferSize);
        break;
      case JCSP:
      default:
        MultibufferCSPDeferredRequest buffer = new MultibufferCSPDeferredRequest(bufferSize);
        sharedResource = buffer;
        ProcessManager pm = new ProcessManager(buffer);
        pm.start();
    }

    // Declaration and creation of producers threads
    Producer[] producers;
    producers = new Producer[N_PRODS];
    for (int i = 0; i < N_PRODS; i++) {
      producers[i] = new Producer(sharedResource, random.nextInt(100)+1);
    }

    // Declaration and creation of consumers threads
    Consumer[] consumers;
    consumers = new Consumer[N_CONSS];
    for (int i = 0; i < N_CONSS; i++) {
      consumers[i] = new Consumer(sharedResource);
    }

    // Starting Threads
    for (int i = 0; i < N_PRODS; i++) {
      producers[i].start();
    }
    
    for (int i = 0; i < N_CONSS; i++) {
      consumers[i].start();
    }
    
    // Wait until processes end
    // really necesary 'cause never ends! 
    try {
      for (int i = 0; i < N_PRODS; i++) {
        producers[i].join();
      }
      for (int i = 0; i < N_CONSS; i++) {
        consumers[i].join();
      }
    } catch (InterruptedException ex) {
      Logger.getLogger(MultibufferRunner.class.getName()).log(
              Level.SEVERE, 
              ex.getMessage(),
              ex);

      System.exit (-1);
    }
  }
         
}
