package es.upm.babel.ccjml.samples.recyclingplant.java;

import java.util.ArrayList;
import java.util.List;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.Guard;
import org.jcsp.lang.ProcessInterruptedException;

/**
 * @author rnnalborodo
 */
public class RecyclingPlantCSP implements RecyclingPlant, CSProcess{

  private int MAX_W_CONTAINER;
  
  private int weight;
  private State state;
  private int accessing;
  
  // CSP attributes 
  // Channel for sending request to the server
  // one for each method
  private final Any2OneChannel chNotifyWeight;
  private final Any2OneChannel chIncrementWeight;
  private final Any2OneChannel chNotifyDrop;
  private final Any2OneChannel chPrepareReplacement;
  private final Any2OneChannel chNotifyReplacement;
  
  private final List<NotifyWeightRequestCSP> notifyWeightRequests = new ArrayList<>();
  private final List<PrepareReplacementRequestCSP> prepareReplacementRequests = new ArrayList<>();
  private final List<IncrementWeightRequestCSP> incrementWeightRequests = new ArrayList<>();

  public RecyclingPlantCSP(){
    this(10);
  }
  
  public RecyclingPlantCSP(int max){
    MAX_W_CONTAINER = max;
    weight = 0;
    state = State.READY;
    accessing = 0;
    
    chNotifyWeight = Channel.any2one();
    chIncrementWeight = Channel.any2one();
    chNotifyDrop = Channel.any2one();
    chPrepareReplacement = Channel.any2one();
    chNotifyReplacement = Channel.any2one();
  }
  
  //@ requires w > 0;
  //@ ensures \result == (weight + w <= MAX_P_CONTAINER && state != State.REPLACING);
  private boolean cpreIncrementWeight(int w){
    return weight + w <= MAX_W_CONTAINER && state != State.REPLACING;
  }
  
  //@ requires w > 0;
  //@ ensures \result == state != State.REPLACING;
  private boolean cpreNotifyWeight(){
    return state != State.REPLACING;
  }
  
  //@ ensures \result ==state == State.TO_REPLACE && accessing == 0;
  private boolean cprePrepareReplacement() {
    return state == State.TO_REPLACE && accessing == 0;
  }
  
  //@ public normal_behaviour 
  //@   requires w > 0;
  //@   cond_sync state != State.REPLACING;
  //@   assignable state;
  /*@   ensures (weight + w > MAX_W_CONTAINER && state = State.TO_REPLACE) ||
     @                (weight + w <= MAX_W_CONTAINER && state = State.READY);
     @*/
  @Override
  public void notifyWeight(int w){
    Any2OneChannel ch = Channel.any2one();
    chNotifyWeight.out().write(new NotifyWeightRequestCSP(ch));
    
    ch.out().write(w);
  }
  
  private void innerNotifyWeight( int w){
    if (weight + w > MAX_W_CONTAINER ) {
      state = State.TO_REPLACE;
      } else {
      state = State.READY;
    }
  }
  
  //@ public normal_behaviour 
  //@   requires w > 0;
  //@   cond_sync weight + w <= MAX && state != State.REPLACING;
  //@   assignable weight;
  //@   ensures weight == \old(weight) + w;
  @Override
  public void incrementWeight(int w){    
    chIncrementWeight.out().write(new IncrementWeightRequestCSP(w));
  }
  
  private void innerIncrementeWeight(int w) {
    weight+= w;
  }
  
  //@ public normal_behaviour 
  //@   assignable accessing;
  //@   ensures accessing == \old(accessing) -1;
  @Override
  public void notifyDrop(){
    chNotifyDrop.out().write(true);
  }
  
  private void innerNotifyDrop(){
    accessing--;
  }
  
  //@ public normal_behaviour
  //@   cond_sync state == State.TO_REPLACE && accessing == 0;
  //@   assignable state;
  //@   ensures state == State.REPLACING;
  @Override
  public void prepareReplacement(){
    chPrepareReplacement.out().write(true);
  }
  
  private void innerPrepareReplacement(){
    state = State.REPLACING;
  }
  
  //@ public normal_behaviour
  //@   requires state == State.REPLACING && accessing == 0 && max > 0;
  //@   assignable weight, state, MAX_W_CONTAINER;
  //@   ensures weight == 0 && state == State.READY && MAX_W_CONTAINER = max;
  @Override
  public void notifyReplacement(int max){
    chNotifyReplacement.out().write(max);
  }
  
  private void innerNotifyReplacement(int max){
    MAX_W_CONTAINER = max;
    weight = 0;
    state = State.READY;
  }
  
  // SERVER code
  private static final int NOTIFY_WEIGHT = 0;
  private static final int INCREMENT_WEIGHT = 1;
  private static final int NOTIFY_DROP = 2;
  private static final int PREPARE_REPLACEMENT = 3;
  private static final int NOTIFY_REPLACEMENT = 4;
  
  private static final int QUEUE_HEAD = 0;
  
  @Override
  public void run() {
    Guard[] inputs = {
          chNotifyWeight.in(),
          chIncrementWeight.in(),
          chNotifyDrop.in(),
          chPrepareReplacement.in(),
          chNotifyReplacement.in(),
        };
    Alternative services = new Alternative(inputs);
    int choice = 0;
    while (true) {
      try {
        choice = services.fairSelect();
      } catch (ProcessInterruptedException e){}

      ChannelInput input;
      switch(choice){
        case NOTIFY_WEIGHT: 
          input = chNotifyWeight.in();
          notifyWeightRequests.add(notifyWeightRequests.size(),(NotifyWeightRequestCSP) input.read());
          break;

        case INCREMENT_WEIGHT: 
          input = chIncrementWeight.in();
          incrementWeightRequests.add(incrementWeightRequests.size(),(IncrementWeightRequestCSP) input.read());
          break;

        case NOTIFY_DROP: 
          //consume the package sent
          chNotifyDrop.in().read();
          innerNotifyDrop();
          break;

        case PREPARE_REPLACEMENT: 
          input = chPrepareReplacement.in();
          prepareReplacementRequests.add(prepareReplacementRequests.size(),(PrepareReplacementRequestCSP) input.read());
          break;

        case NOTIFY_REPLACEMENT: 
          // waiting requests must not exist
          int newContainerWeight = (Integer) chNotifyReplacement.in().read();
          innerNotifyReplacement(newContainerWeight);
          break;
      }
      
      boolean anyResumed = true;
      while (anyResumed) {
        anyResumed = false;
        
        // trying to process notifyWeight requests
        int lastItem = notifyWeightRequests.size();
        for (int i = 0; i < lastItem; i++) {
          
          NotifyWeightRequestCSP notifierCrank = notifyWeightRequests.get(QUEUE_HEAD);
          notifyWeightRequests.remove(QUEUE_HEAD);
          
          if (cpreNotifyWeight()){
            ChannelInput chIn = notifierCrank.getChannel().in();
            int _weight = (Integer)chIn.read();
            innerNotifyWeight(_weight);
            anyResumed = true; 
          } else {
            notifyWeightRequests.add(notifyWeightRequests.size(), notifierCrank);
          }
        }

        // trying to process incrementWeight requests
        lastItem = incrementWeightRequests.size();
        for (int i = 0; i < lastItem; i++) {
          
          IncrementWeightRequestCSP incrementerCrank = incrementWeightRequests.get(QUEUE_HEAD);
          incrementWeightRequests.remove(QUEUE_HEAD);
          
          if (cpreIncrementWeight(incrementerCrank.getWeight())){
            innerNotifyWeight(incrementerCrank.getWeight());
            anyResumed = true; 
          } else {
            incrementWeightRequests.add(incrementWeightRequests.size(), incrementerCrank);
          }
        }
        // trying to process prepareReplacement requests
        lastItem = prepareReplacementRequests.size();
        for (int i = 0; i < lastItem; i++) {
          PrepareReplacementRequestCSP containerController = prepareReplacementRequests.get(QUEUE_HEAD);
          prepareReplacementRequests.remove(QUEUE_HEAD);
          
          if (cprePrepareReplacement()){
            innerPrepareReplacement();
            anyResumed = true; 
          } else {
            prepareReplacementRequests.add(prepareReplacementRequests.size(), containerController);
          }
        }
      }
    }
  }
}
