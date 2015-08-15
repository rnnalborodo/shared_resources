package es.upm.babel.ccjml.samples.bufferoddeven.java;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Queue;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.AltingChannelInput;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.One2OneChannel;

public class BufferOddEvenCSPDeferredRequest implements BufferOddEven, CSProcess {

  /** WRAPPER Implementation */
  private final Any2OneChannel chPut;
  private final Any2OneChannel chGet;
  /** 
   * List for enqueue all request for each method
   */
  private final Queue<PutRequestCSP> putRequest = new ArrayDeque<>();
  private final Queue<GetRequestCSP> getRequest = new ArrayDeque<>();

  private int MAX;

  private int buffer[]; /*@ in data; @*/
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

  public BufferOddEvenCSPDeferredRequest(){
    this(10);
  }

  public BufferOddEvenCSPDeferredRequest(int m){
    MAX = m;
    buffer = new int[MAX];
    first = 0;
    nData = 0;

    chPut = Channel.any2one();
    chGet = Channel.any2one();  
  }

  /*@ public normal_behaviour
    @  ensures \result == nData <= MAX - 1;
    @*/
  private boolean cprePut() {
    return nData <= MAX - 1;
  }

  /*@ public normal_behaviour
    @  requires t == EVEN || t == ODD;
    @  ensures (t == ODD && \result == buffer[first] % 2 == 1) || 
    @          (t == EVEN && \result == buffer[first] % 2 == 0)  ;
    @*/
  private boolean cpreGet(Type t) {
    return nData > 0 && ((buffer[first] % 2 == 0 && t == Type.EVEN) || 
           (buffer[first] % 2 == 1 && t == Type.ODD));
  }

  @Override
  public void put(int d) {
    //@ assume true && invariant();
    One2OneChannel innerChannel = Channel.one2one();
    chPut.out().write(new PutRequestCSP(d, innerChannel));
    
    innerChannel.in().read();
  }

  @Override
  public int get(Type t) {
    //@ assume true && invariant();
    One2OneChannel innerChannel = Channel.one2one();
    chGet.out().write(new GetRequestCSP(t, innerChannel));
    
    return (Integer)innerChannel.in().read();
  }

  /** SERVER IMPLEMENTATION */
  private final int PUT = 0;
  private final int GET = 1;
  private final int QUEUE_HEAD = 2;

  @Override
  public void run() {
    //One entry for each associated predicated
    AltingChannelInput[] inputs = {
        chPut.in(), 
        chGet.in()
    };
    Alternative services = new Alternative(inputs);
    int chosenService = 0;
    ChannelInput cresp;

    while (true) {

      chosenService = services.fairSelect();

      switch (chosenService){
        case PUT:
          cresp = chPut.in();
          putRequest.offer((PutRequestCSP) cresp.read());
          break;
        case GET:
          cresp = chGet.in();
          getRequest.offer((GetRequestCSP) cresp.read());
          break;
      }
      
      /**
       * Unblocking code
       * Must always process all request which is associated CPRE holds
       */
      boolean anyResumed;
      do {
        anyResumed = false;
        
        for(PutRequestCSP rq : putRequest){
          
          if (nData < MAX){
            putRequest.remove(rq);
            //@ assert nData < MAX;

            buffer[(first +nData)%MAX] = rq.getFst();
            nData++;

            rq.getChannel().out().write(null);
            anyResumed = true; 
          } 
        }
        
        for(GetRequestCSP rq : getRequest){
          if (nData > 0){
            if ( (buffer[first] % 2 == 0 && rq.getType() == Type.EVEN ) ||
                (buffer[first] % 2 == 1 && rq.getType() == Type.ODD )){
              //@ assert cpreGet(rq.getType());
              getRequest.remove(rq);
              rq.getChannel().out().write(this.innerGet());
              anyResumed = true;
            }  
          } 
        }
        
      } while (anyResumed);
      
    }// FIN BUCLE SERVICIO
  }// FIN SERVIDOR
  
  private int innerGet(){
    int res = buffer[first];
    first ++;
    first%=MAX;
    nData--;
    return res;
  }
  
  @Override
  public String toString(){
    return "buffer = " + Arrays.toString(buffer) + 
           "(fst = " + first + ", nData = " +nData+")";
  }
}
