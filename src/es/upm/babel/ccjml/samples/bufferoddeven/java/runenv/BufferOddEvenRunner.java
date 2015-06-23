package es.upm.babel.ccjml.samples.bufferoddeven.java.runenv;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.jcsp.lang.ProcessManager;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEven;
import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEvenCSP;
import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEvenMonitor;
import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEvenSync;

/**
 * Main class for BufferOddEven problem. This class generates consumers and 
 * producers to execute and test the shared resource implementation
 * @author rnnalborodo
 */
public class BufferOddEvenRunner {
  
  public enum ImplementationType {SYNCHRONIZED, MONITOR, JCSP};
  
  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());
  
  public static final void main(final String[] args) {
    /** ARG 0
     * Represents the chosen implementation to test
     * 0-> Synchronized methods
     * 1-> using monitors
     * 2-> JSCP message passing
     */
    ImplementationType implementation;
    if (args.length == 0 ){
      Logger.getLogger(BufferOddEvenRunner.class.getName()).log(
              Level.SEVERE, 
              "Wrong invocation. Implementation using Synchronization methods will be used");
      implementation = ImplementationType.JCSP;
    } else {
      switch (args[0]) {
        case "sync":
        case "0":
          implementation = ImplementationType.SYNCHRONIZED;
          break;
        case "mon":
        case "1":
          implementation = ImplementationType.MONITOR;
          break;
        default:
          implementation = ImplementationType.JCSP;
          break;
      }
    }
    
    /** ARGS [1] buffer capacity
     * 
     */
    int N;
    try {
      N = Integer.parseInt(args[1]);
    } catch (NumberFormatException |  java.lang.ArrayIndexOutOfBoundsException ex) {
       Logger.getLogger(BufferOddEvenRunner.class.getName()).log(
              Level.SEVERE, 
              "Wrong invocation. 10 as buffer size will be used");
      N = 3;
    }
    
    // setting numbers of consumers and producers
    final int N_PRODS = 1;
    final int N_CONSS = 2;

    // Shared resource. Implementation selected based on input
    final BufferOddEven sharedResource;
    switch (implementation){
      case SYNCHRONIZED:
        sharedResource = new BufferOddEvenSync(N);
        break;
      case MONITOR:
        sharedResource = new BufferOddEvenMonitor(N);
        break;
      default:
        BufferOddEvenCSP buffer = new BufferOddEvenCSP(N);
        sharedResource = buffer;
        ProcessManager pm = new ProcessManager(buffer);
        pm.start();
    }

    // Declaration and creation of producers threads
    Producer[] producers;
    producers = new Producer[N_PRODS];
    for (int i = 0; i < N_PRODS; i++) {
      producers[i] = new Producer(sharedResource, random.nextInt(100));
    }

    // Declaration and creation of consumers threads
    Consumer[] consumers;
    consumers = new Consumer[N_CONSS];
    for (int i = 0; i < N_CONSS; i++) {
      consumers[i] = new Consumer(sharedResource, (i%2 == 0)?BufferOddEven.Type.EVEN:BufferOddEven.Type.ODD);
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
      Logger.getLogger(BufferOddEvenRunner.class.getName()).log(
              Level.SEVERE, 
              ex.getMessage(),
              ex);

      System.exit (-1);
    }
  }
         
}
