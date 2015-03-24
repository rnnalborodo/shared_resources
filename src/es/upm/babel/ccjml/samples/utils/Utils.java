package es.upm.babel.ccjml.samples.utils;

import java.util.logging.Level;
import java.util.logging.Logger;

import es.upm.babel.ccjml.samples.bufferoddeven.java.runenv.BufferOddEvenRunner;

/**
 * @author rnnalborodo
 */
public class Utils {
  
  public enum ImplementationType {SYNCHRONIZED, MONITOR, JCSP};

  public static Object[] argumentsVerifier(String args[], Class classObject ){
    ImplementationType implementationType;
    int bufferSize;
    
    if (args.length != 2 ){
      Logger.getLogger(classObject.getName()).log(
              Level.SEVERE, "USAGE: {0} <implementation> <buffer_size>\n"
                      + "implementation = sync | mon | jcsp | default\n"
                      + "Using synchronization methods implementation and buffer size \"10\" instead ", classObject.getCanonicalName());
      implementationType = ImplementationType.MONITOR;
      bufferSize = 3;
    } else {

      // ARG 0 -> Represents the chosen implementation to test
      switch (args[0]) {
        case "jcsp":
        case "2":
          implementationType = ImplementationType.JCSP;
          break;
        case "mon":
        case "1":
          implementationType = ImplementationType.MONITOR;
          break;
        case"sync":
        case"0":
        default:
          implementationType = ImplementationType.SYNCHRONIZED;
      }

      //ARGS [1] buffer capacity
      try {
        bufferSize = Integer.parseInt(args[1]);
      } catch (NumberFormatException |  java.lang.ArrayIndexOutOfBoundsException ex) {
         Logger.getLogger(BufferOddEvenRunner.class.getName()).log(
                Level.SEVERE, 
                "Wrong invocation. 10 as buffer size will be used");
        bufferSize = 3;
      }
    }
    
    Object[] res = {implementationType, bufferSize};
    return res;
  }
}
