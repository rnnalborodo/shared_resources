package es.upm.babel.ccjml.samples.bufferoddeven.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.AltingChannelInput;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelOutput;
import org.jcsp.lang.One2OneChannel;
import org.jcsp.lang.ProcessInterruptedException;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEven.Type;

public class BufferOddEvenCSP implements BufferOddEven, CSProcess {

  /** WRAPPER Implementation */
  private final Any2OneChannel chPut;
  private final Any2OneChannel chGetEven;
  private final Any2OneChannel chGetOdd;

  private int MAX;
  /*@ private represents maxData <- TAM; @*/

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

  public BufferOddEvenCSP(){
    this(10);
  }

  public BufferOddEvenCSP(int m){
    MAX = m;
    buffer = new int[MAX];
    first = 0;
    nData = 0;

    chPut = Channel.any2one();
    chGetEven = Channel.any2one();
    chGetOdd = Channel.any2one();  
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
    return nData > 0 && ((buffer[first] % 2 == 0 && t == Type.EVEN) || (buffer[first] % 2 == 1 && t == Type.ODD));
  }

  @Override
  public void put(int d) {
    chPut.out().write(d);
  }

  @Override
  public int get(Type t) {
    One2OneChannel chResp = Channel.one2one();
    if (t.equals(Type.EVEN)) {
      chGetEven.out().write(chResp.out());
    } else {
      chGetOdd.out().write(chResp.out());
    }

    return (Integer)chResp.in().read();
  }

  /** SERVER IMPLEMENTATION */
  private final int GET_EVEN = 0;
  private final int GET_ODD = 1;
  private final int PUT = 2;

  @Override
  public void run() {
    /* 
     * One entry for each associated predicated. 
     * Union of all channel lists.
     */
    AltingChannelInput[] inputs = {
        chGetEven.in(), 
        chGetOdd.in(), 
        chPut.in()
    };
    Alternative services = new Alternative(inputs);
    int chosenService = 0;
    ChannelOutput cresp;
    
    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean[] syncCond = new boolean[3];
    syncCond[GET_EVEN] = cpreGet(Type.EVEN);
    syncCond[GET_ODD] = cpreGet(Type.ODD) ;
    syncCond[PUT] = nData < MAX;
    

    while (true) {
      syncCond[GET_EVEN] = cpreGet(Type.EVEN);
      syncCond[GET_ODD] = cpreGet(Type.ODD) ;
      syncCond[PUT] = nData < MAX;
      
      chosenService = services.fairSelect(syncCond);

      switch (chosenService){
        case GET_EVEN:
          //@ assume cpreGet(Type.EVEN);
          cresp =(ChannelOutput) chGetEven.in().read();
          cresp.write(innerGet());
          break;
        case GET_ODD:
          //@ assume cpreGet(Type.ODD);
          cresp =(ChannelOutput) chGetOdd.in().read();
          cresp.write(innerGet());
          break;
        case PUT:
          //@ assume cprePut();
          int d = (Integer) chPut.in().read();
          buffer[(first +nData)%MAX] = d;
          nData++;
      }
    }// FIN BUCLE SERVICIO
  }// FIN SERVIDOR
  
  private int innerGet(){
    int res = buffer[first];
    first ++;
    first%=MAX;
    nData--;
    return res;
  }
}
