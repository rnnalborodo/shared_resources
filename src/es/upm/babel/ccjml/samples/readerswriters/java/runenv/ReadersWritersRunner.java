package es.upm.babel.ccjml.samples.readerswriters.java.runenv;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.jcsp.lang.ProcessManager;

import es.upm.babel.ccjml.samples.bufferoddeven.java.runenv.BufferOddEvenRunner;
import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWriters;
import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWritersCSP;
import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWritersMonitor;
import es.upm.babel.ccjml.samples.readerswriters.java.ReadersWritersSync;
import es.upm.babel.ccjml.samples.utils.Utils;

/**
 * Main class for <em>BoundedBuffer</em> problem. This class generates consumers and 
 * producers to execute and test the shared resource implementation
 * @author rnnalborodo
 */
public class ReadersWritersRunner {
  
  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());
  
  public static final void main(final String[] args) {
   
    //cheking arguments
    Utils.ImplementationType implementation;
    
    if (args.length != 1 ){
      Logger.getLogger(ReadersWritersRunner.class.getName()).log(
              Level.SEVERE, "USAGE: {0} <implementation> <buffer_size>\n"
                      + "implementation = sync | mon | jcsp | default", ReadersWritersRunner.class.getName());
//      implementation = Utils.ImplementationType.SYNCHRONIZED;
      implementation = Utils.ImplementationType.JCSP;
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
    final int N_WRITERS = 10;
    final int N_READERS = 3;

    // Shared resource. Implementation selected based on input
    final ReadersWriters sharedResource;
    switch (implementation){
      case SYNCHRONIZED:
        sharedResource = new ReadersWritersSync();
        break;
      case MONITOR:
        sharedResource = new ReadersWritersMonitor();
        break;
      case JCSP:
      default:
        ReadersWritersCSP manager = new ReadersWritersCSP();
        sharedResource = manager;
        ProcessManager pm = new ProcessManager(manager);
        pm.start();
    }

    // Declaration and creation of producers threads
    Writer[] writers;
    writers = new Writer[N_WRITERS];
    for (int i = 0; i < N_WRITERS; i++) {
      writers[i] = new Writer(sharedResource);
    }

    // Declaration and creation of consumers threads
    Reader[] readers;
    readers = new Reader[N_READERS];
    for (int i = 0; i < N_READERS; i++) {
      readers[i] = new Reader(sharedResource);
    }

    // Starting Threads
    for (int i = 0; i < N_WRITERS; i++) {
      writers[i].start();
    }
    
    for (int i = 0; i < N_READERS; i++) {
      readers[i].start();
    }
    
    // Wait until processes end
    // really necesary 'cause never ends! 
    try {
      for (int i = 0; i < N_WRITERS; i++) {
        writers[i].join();
      }
      for (int i = 0; i < N_READERS; i++) {
        readers[i].join();
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
