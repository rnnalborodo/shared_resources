package es.upm.babel.ccjml.samples.warehouse.java;

import java.util.ArrayList;
import java.util.List;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.Guard;

import es.upm.babel.ccjml.samples.multibuffer.java.GetRequestCSP;

public class WarehouseAccessControlCSPDeferredRequests  
                        implements WarehouseAccessControl, CSProcess {
  
  /** WRAPPER IMPLEMENTATION */      
  /**
   *  Channel for receiving external request for each method
   */
  public static final int N_ROBOTS = Robots.N_ROBOTS;
  public static final int N_WAREHOUSE = Robots.N_WAREHOUSE;
  public static final int MAX_WEIGHT = Robots.MAX_WEIGHT_IN_WAREHOUSE;

  private Any2OneChannel chEnterWarehouse; 
  private Any2OneChannel chExitWarehouse;

  /** 
   * List for enqueue all request for each method
   */
  private final List<EnterWarehousePetition> enterWarehouseRequests 
                                                  = new ArrayList<>();
  private final List<ExitWarehousePetition> exitWarehouseRequests
                                                  = new ArrayList<>();

  private int weight[];
  private boolean occupied[];
  
  public WarehouseAccessControlCSPDeferredRequests() {
    weight = new int[N_WAREHOUSE];
    occupied = new boolean[N_WAREHOUSE];
    
    chEnterWarehouse = Channel.any2one();
    chExitWarehouse = Channel.any2one();
  }  


  public void enterWarehouse(int n, int w) {
    EnterWarehousePetition pet = 
            new EnterWarehousePetition(n,w, Channel.one2one());
    // sending petition to the server
    chEnterWarehouse.out().write(pet);
    // waiting for notification
    pet.getChannel().in().read();
  }
  
  public void exitWarehouse(int n, int w) {
    ExitWarehousePetition pet = 
            new ExitWarehousePetition(n, Channel.one2one());
    // sending petition to the server
    chExitWarehouse.out().write(pet);
    // sending the weight
    pet.getChannel().out().write(w);
    // waiting for notification
    pet.getChannel().in().read();  
   }
  
  /* SERVER IMPLEMENTATION */
  /** Constants representing API method's */
  private static final int ENTER = 0;
  private static final int EXIT = 1;
  private static final int QUEUE_HEAD = 0;

  public void run() {
    /* One entry for each method. */
    Guard[] inputs = { chEnterWarehouse.in(), 
                       chExitWarehouse.in() };
    Alternative services = new Alternative(inputs);

    while (true) {
      int chosenService = services.fairSelect();
      
      // receiving a petition from the wrapper 
      switch (chosenService) {
        case ENTER:
          EnterWarehousePetition enterRequest = 
                (EnterWarehousePetition) chEnterWarehouse.in().read();
          enterWarehouseRequests.add(enterRequest);
          break;
  
        case EXIT:
          ExitWarehousePetition exitRequest = 
                (ExitWarehousePetition) chExitWarehouse.in().read();
          exitWarehouseRequests.add(exitRequest);
          break;
      }
      
      /**
       * Must always process all request which is 
       * associated CPRE holds
       */
      boolean anyResumed;
      do {
        anyResumed = false;
        // processing exitWarehouse requests
        int lastItem = exitWarehouseRequests.size();
        for (int i = 0; i < lastItem; i++) {
          ExitWarehousePetition current = 
                                  exitWarehouseRequests.get(QUEUE_HEAD);
          exitWarehouseRequests.remove(QUEUE_HEAD);

          if (current.getWarehouse() == N_WAREHOUSE ||
              !occupied[current.getWarehouse()+1]){
            /*@ assert current.getWarehouse() == N_WAREHOUSE ||
              @        !occupied[current.getWarehouse()+1];
              @*/
            ChannelInput chIn = current.getChannel().in();
            int cWeight = ((Integer)chIn.read());
            
            // performing the changes on the resource
            // updating the current weight of the warehouse
            weight[current.getWarehouse()] -= cWeight;
            
            // updating the leaving corridor iff the robot exits any inner warehouse
            if ( current.getWarehouse() != Robots.N_WAREHOUSE -1 )
              occupied[current.getWarehouse()] = true;

            // sending the notification
            current.getChannel().out().write(null);
            anyResumed = true; 
          } else {
            exitWarehouseRequests.add(exitWarehouseRequests.size(), 
                                      current);
          }
        }
        
        // processing enterWarehouse requests
        lastItem = enterWarehouseRequests.size();
        for (int i = 0; i < lastItem; i++) {
          EnterWarehousePetition current = 
                              enterWarehouseRequests.get(QUEUE_HEAD);
          enterWarehouseRequests.remove(QUEUE_HEAD);

          if (current.getWeight() + weight[current.getWarehouse()] 
                                                            <= MAX_WEIGHT){
            /*@ assert current.getWeight() + 
              @        weight[current.getWarehouse()]
              @                                      <= MAX_WEIGHT;
              @*/
            
            // performing the changes on the resource
            if (current.getWarehouse() != 0)
              occupied[current.getWarehouse()-1] = false;
            // updating warehouse current weight
            weight[current.getWarehouse()] += current.getWeight();
            
            // sending the notification
            current.getChannel().out().write(null);
            anyResumed = true; 
          } else {
            enterWarehouseRequests.add(enterWarehouseRequests.size(), 
                                       current);
          }
        }
  
        /*@ assert (\forall int i; 
          @                 i >= 0 && i <= enterWarehouseRequests.size(); 
          @                 enterWarehouseRequests.get(i).getWeight() + 
          @                 weight[enterWarehouseRequests.get(i).getWarehouse()]
          @                                                        <= MAX_WEIGH);
          @*/
        /*@ assert (\forall int i; 
          @                 i >= 0 && i <= exitWarehouseRequests.size(); 
          @                 exitWarehouseRequests.get(i).getWarehouse() 
          @                                                   == N_WAREHOUSE ||
          @           !occupied[exitWarehouseRequests.get(i).getWarehouse()+1]);
          @*/
      } while (anyResumed);
    } // end server loop
  } // end server
}
