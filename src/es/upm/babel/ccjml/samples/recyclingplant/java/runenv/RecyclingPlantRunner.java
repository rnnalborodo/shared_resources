package es.upm.babel.ccjml.samples.recyclingplant.java.runenv;

import java.util.Calendar;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.jcsp.lang.ProcessManager;

import es.upm.babel.ccjml.samples.bufferoddeven.java.runenv.BufferOddEvenRunner;
import es.upm.babel.ccjml.samples.recyclingplant.java.RecyclingPlant;
import es.upm.babel.ccjml.samples.recyclingplant.java.RecyclingPlantCSP;
import es.upm.babel.ccjml.samples.recyclingplant.java.RecyclingPlantMonitor;
import es.upm.babel.ccjml.samples.recyclingplant.java.RecyclingPlantSync;
import es.upm.babel.ccjml.samples.utils.Utils;

/**
 * Main class for <em>RecyclingPlant</em> problem. This class generates cranks and 
 * containers to execute and test the shared resource implementations
 * @author rnnalborodo
 */
public class RecyclingPlantRunner {
  
  private static final java.util.Random random = new java.util.Random(Calendar.getInstance().getTimeInMillis());
  
  public static final void main(final String[] args) {
   
    //cheking arguments
    Utils.ImplementationType implementation;
    int maxWeightContainer;
    
    if (args.length != 2 ){
      Logger.getLogger(RecyclingPlantRunner.class.getName()).log(
              Level.SEVERE, "USAGE: {0} <implementation> \n"
                      + "implementation = sync | mon | jcsp | default\n"
                      + "Using synchronization methods implementation", RecyclingPlantRunner.class.getName());
      implementation = Utils.ImplementationType.JCSP;
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
          //ARGS [1] buffer capacity
    try {
      maxWeightContainer = Integer.parseInt(args[1]);
    } catch (NumberFormatException |  java.lang.ArrayIndexOutOfBoundsException ex) {
       Logger.getLogger(RecyclingPlantRunner.class.getName()).log(
              Level.SEVERE, 
              "Wrong invocation. 3000 as the available weight for the first container");
      maxWeightContainer = 3000;
    }
      
    // setting numbers of cranks and containers
    final int N_CONTAINERS = 1;

    // Shared resource. Implementation selected based on input
    final RecyclingPlant sharedResource;
    switch (implementation){
      case SYNCHRONIZED:
        sharedResource = new RecyclingPlantSync(maxWeightContainer);
        break;
      case MONITOR:
        sharedResource = new RecyclingPlantMonitor(maxWeightContainer);
        break;
      case JCSP:
      default:
        RecyclingPlantCSP buffer = new RecyclingPlantCSP(maxWeightContainer);
        sharedResource = buffer;
        ProcessManager pm = new ProcessManager(buffer);
        pm.start();
    }

    // Declaration and creation of producers threads
    CranksController[] cranks;
    cranks = new CranksController[Crank.MAX_CRANKS];
    for (int i = 0; i < Crank.MAX_CRANKS; i++) {
      try {
        cranks[i] = new CranksController(i, sharedResource);
      } catch (Exception ex){
        Logger.getLogger(RecyclingPlantRunner.class.getName()).log(
              Level.SEVERE, 
              null,
              ex
        );
      }
    }

    // Declaration and creation of consumers threads
    ContainersController[] containers;
    containers = new ContainersController[N_CONTAINERS];
    for (int i = 0; i < N_CONTAINERS; i++) {
      containers[i] = new ContainersController(sharedResource);
    }

    // Starting Threads
    for (int i = 0; i < Crank.MAX_CRANKS; i++) {
      cranks[i].start();
    }
    
    for (int i = 0; i < N_CONTAINERS; i++) {
      containers[i].start();
    }
    
    // Wait until processes end
    // really necesary 'cause never ends! 
    try {
      for (int i = 0; i < Crank.MAX_CRANKS; i++) {
        cranks[i].join();
      }
      for (int i = 0; i < N_CONTAINERS; i++) {
        containers[i].join();
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
