package es.upm.babel.ccjml.samples.multibuffer.java;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.logging.Logger;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;
import org.jcsp.lang.ProcessInterruptedException;

import es.upm.babel.cclib.ConcIO;
  
/** 
 * Multibuffer implementation JCSP Library with deferred request processing. 
 *
 * @author BABEL Group
 */
public class MultibufferCSPDeferredRequest extends AMultibuffer implements CSProcess {

  /** WRAPPER IMPLEMENTATION */      
  /**
   *  Channel for receiving external request for each method
   */
  private final Any2OneChannel chPut = Channel.any2one();
  private final Any2OneChannel getChannel = Channel.any2one();

  /** 
   * List for enqueue all request for each method
   */
  private final List<PutRequestCSP> producersRequest = new ArrayList<>();
  private final List<GetRequestCSP> consumersRequest = new ArrayList<>();

  //@ public normal_behaviour
  //@ ensures \result == maxData > 0 && data.length() <= maxData;
  //@ public model pure boolean invariant();  
  public MultibufferCSPDeferredRequest(int _max) {
    MAX = _max;
    buffer = new Object[_max];
    first =0;
    nData = 0;
  }

  @Override
  public void put(Object[] els) {
    //@assume els.length <= maxData / 2 && invariant();
    One2OneChannel innerChannel = Channel.one2one();
    chPut.out().write(new PutRequestCSP(els.length,innerChannel));
    // data to be inserted
    innerChannel.out().write(els);
    innerChannel.in().read();
    //@ assert data == \old(data).concat(JMLObjectSequence.convertFrom(els)) && invariant();
  }

  @Override
  public Object[] get(int n) {
    //@ assume (n <= maxData / 2) && invariant();
    One2OneChannel innerChannel = Channel.one2one();
    getChannel.out().write(new GetRequestCSP(n,innerChannel));
    Object[] res = (Object[]) innerChannel.in().read();
    //@ assert \result.length == n && JMLObjectSequence.convertFrom(\result).concat(data) == \old(data) && invariant();
    return res;
  }

  /* SERVER IMPLEMENTATION */
  /** Constants representing API method's */
  private static final int PUT = 0;
  private static final int GET = 1;
  private static final int QUEUE_HEAD = 0;

  @Override
  public void run() {
    /* One entry for each method. */
    Guard[] inputs = {
      chPut.in(),
      getChannel.in()
    };
    Alternative services = new Alternative(inputs);
    int chosenService = 0;
    
    while (true){
      chosenService = services.fairSelect();
      switch(chosenService){
        case PUT: 
          ChannelInput inputProducers = chPut.in();
          producersRequest.add(producersRequest.size(),(PutRequestCSP) inputProducers.read());
          break;
  
        case GET:
          ChannelInput inputConsumers = getChannel.in();
          consumersRequest.add(consumersRequest.size(),(GetRequestCSP) inputConsumers.read());
          break;
      }
  
      /**
       * Unblocking code
       * Must always process all request which is associated CPRE holds
       */
      boolean anyResumed;
      do {
        anyResumed = false;
  
        int lastItem = producersRequest.size();
        for (int i = 0; i < lastItem; i++) {
          PutRequestCSP currentProducer = producersRequest.get(QUEUE_HEAD);
          producersRequest.remove(QUEUE_HEAD);

          if (currentProducer.getFst() <= MAX - nData){
            //@ assume (els.length <= maxData / 2) && invariant() && (els.length <= nSlots());
            ChannelInput chIn = currentProducer.getSnd().in();
            Object[] items = (Object[])chIn.read();
            this.innerPut(items);
            currentProducer.getChannel().out().write(null);
            anyResumed = true; 
          } else {
            producersRequest.add(producersRequest.size(), currentProducer);
          }
        }
  
        lastItem = consumersRequest.size();
        for (int i = 0; i < lastItem; i++) {
          GetRequestCSP currentConsumer = consumersRequest.get(QUEUE_HEAD);
          consumersRequest.remove(QUEUE_HEAD);
          
          if (currentConsumer.getFst() <= nData){
            //@ assume (n <= maxData / 2) && invariant() &&  n <= nData();
            currentConsumer.getSnd().out().write(this.innerGet(currentConsumer.getFst()));
            anyResumed = true;
          } else {
            consumersRequest.add(consumersRequest.size(), currentConsumer);
          }
        }
        //@ assert (\forall int i; i >= 0 && i <= producersRequest.size(); producersRequest.get(i).fst > max - buffer.length);
        //@ assert (\forall int i; i >= 0 && i <= consumersRequest.size(); consumersRequest.get(i).fst > buffer.length);
      } while (anyResumed);
    }
  }

  //@ requires els <= max - buffer.length;
  private void innerPut(Object[] els){
    for (Object el : els) {
      buffer[(first + nData) % MAX] = el;
      nData++;
    }
  }

  //@ requires n <= buffer.length;
  private Object[] innerGet(int n){
    Object[] result = new Object[n];
    for (int j = 0; j < n; j++) {
      result[j] = buffer[first];
      buffer[first] = null;
      first++;
      first %= MAX;
    }
    nData -= n;
    return result;
  }
}
