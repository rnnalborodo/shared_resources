  package es.upm.babel.ccjml.samples.multibuffer.java;

  //  begin{jml_clause:classSR}
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
  
public class MultibufferCSPDeferredRequest implements Multibuffer, CSProcess {

  private final Logger log = Logger.getLogger(MultibufferCSPDeferredRequest.class.getName());
      
  private final Any2OneChannel putChannel = Channel.any2one();
  private final Any2OneChannel getChannel = Channel.any2one();
  private static int max;
  /*@ private represents maxData <- max; @*/
  //  end{jml_clause:classSR}
  private Object buffer[]; /*@ in data; @*/
  /*@ private represents
  @   data <- nData == 0
  @     ? JMLObjectSequence.EMPTY 
  @     : first + nData <= max   
  @     ? JMLObjectSequence.convertFrom(buffer).subsequence(first, first + nData - 1)
  @     : JMLObjectSequence.convertFrom(buffer).subsequence(first, maxData - 1).
  @     concat(JMLObjectSequence.convertFrom(buffer,(first + nData) % max - 1)); 
  @*/
  private int first;/*@ in data; @*/
  private int nData;/*@ in data; @*/
  //  begin{jml_clause:classBody}
  private final List<PutRequestCSP> producersRequest = new ArrayList<>();
  private final List<GetRequestCSP> consumersRequest = new ArrayList<>();
  //  end{jml_clause:classBody}

  @Override
  public int maxData() {
    return max;
  }

  //@ public normal_behaviour
  //@ ensures \result == maxData > 0 && data.length() <= maxData;
  //@ public model pure boolean invariant();  
  public MultibufferCSPDeferredRequest(int _max) {
    max = _max;
    buffer = new Object[_max];
    first =0;
    nData = 0;
  }

  //  begin{jml_clause:classConst}
  @Override
  public void put(Object[] els) {
    log.info(Thread.currentThread().getId() +")  Put(" +Arrays.toString(els)+")");
    //@assume els.length <= maxData / 2 && invariant();
    One2OneChannel innerChannel = Channel.one2one();
    putChannel.out().write(new PutRequestCSP(els.length,innerChannel));
    // data to be inserted
    innerChannel.out().write(els);
    log.info(Thread.currentThread().getId() +")  Put(" +Arrays.toString(els)+") ++++++++++");
    //@ assert data == \old(data).concat(JMLObjectSequence.convertFrom(els)) && invariant();
  }

  @Override
  public Object[] get(int n) {
    log.info(Thread.currentThread().getId() +")  GET(" +n +")");
    //@ assume (n <= maxData / 2) && invariant();
    One2OneChannel innerChannel = Channel.one2one();
    getChannel.out().write(new GetRequestCSP(n,innerChannel));
    Object[] res = (Object[]) innerChannel.in().read();
    log.info(Thread.currentThread().getId() +")  GET(" +n+")");
    //@ assert \result.length == n && JMLObjectSequence.convertFrom(\result).concat(data) == \old(data) && invariant();
    return res;
  }

  //  end{jml_clause:classConst}
  //server side code
  private static final int PUT = 0;
  private static final int GET = 1;
  private static final int QUEUE_HEAD = 0;

  //  begin{jml_clause:classServer}
  @Override
  public void run() {
    Guard[] inputs = {
      putChannel.in(),
      getChannel.in()
    };
    Alternative servicios = new Alternative(inputs);
    int choice = 0;
    while (true) {
      try {
        choice = servicios.fairSelect();
      } catch (ProcessInterruptedException e){}

      switch(choice){
        case PUT: 
          ChannelInput inputProducers = putChannel.in();
          producersRequest.add(producersRequest.size(),(PutRequestCSP) inputProducers.read());
          break;

        case GET:
          ChannelInput inputConsumers = getChannel.in();
          consumersRequest.add(consumersRequest.size(),(GetRequestCSP) inputConsumers.read());
          break;
      }

      boolean anyResumed = false;
      do {
        anyResumed = false;

        int lastItem = producersRequest.size();
        for (int i = 0; i < lastItem; i++) {
          PutRequestCSP currentProducer = producersRequest.get(QUEUE_HEAD);
          producersRequest.remove(QUEUE_HEAD);
          
          if (currentProducer.getFst() <= max - nData){
            //@ assume (els.length <= maxData / 2) && invariant() && (els.length <= nSlots());
            ChannelInput chIn = currentProducer.getSnd().in();
            Object[] items = (Object[])chIn.read();
            this.innerPut(items);
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
    //  end{jml_clause:classServer}
    }
  }

    //@ requires els <= max - buffer.length;
  private void innerPut(Object[] els){
    for (Object el : els) {
      buffer[(first + nData) % max] = el;
      nData++;
    }
  }

    //@ requires n <= buffer.length;
  private /*@ spec_public @*/Object[] innerGet(int n){
    Object[] result = new Object[n];
    for (int j = 0; j < n; j++) {
      result[j] = buffer[first];
      buffer[first] = null;
      first++;
      first %= max;
    }
    nData -= n;
    return result;
  }
}
