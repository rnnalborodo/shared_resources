package es.upm.babel.ccjml.samples.multibuffer.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelOutput;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;

/** 
 * Multibuffer implementation using JCSP Library with channel expansion. 
 *
 * @author BABEL Group
 */
public class MultibufferCSP extends AMultibuffer implements CSProcess {
    
  /** WRAPPER IMPLEMENTATION */
  private final Any2OneChannel[] chPut;
  private final Any2OneChannel[] chGet;

  public MultibufferCSP() {
    this(10);
  }

  public MultibufferCSP(int l) {
    this.MAX = l;
    chPut = new Any2OneChannel[MAX/2];
    chGet = new Any2OneChannel[MAX/2];

    for (int n = 0; n < MAX/2; n++) {
      chPut[n] = Channel.any2one();
      chGet[n] = Channel.any2one();
    }

    buffer = new Object[MAX];

    first = 0;
    nData = 0;
  }

  @Override
  public void put(Object[] objs) {
    //@ assume obj.length <= maxData / 2;
    chPut[objs.length - 1].out().write(objs);
  }

  @Override
  public Object[] get(int n) {
    //@ assume n <= maxData / 2;
    Object[] result;
    One2OneChannel chResp = Channel.one2one();
    chGet[n - 1].out().write(chResp.out());
    result = (Object[]) chResp.in().read();
    return result;
  }

  public boolean cprePut(int n) {
    return (MAX - nData) >= n;
  }

  public boolean cpreGet(int n) {
    return nData >= n;
  }

  /** SERVER IMPLEMENTATION */
  @Override
  public void run() {
    /* 
     * One entry for each associated predicated. 
     * Union of all channel lists.
     *
     * Channel splitting positions
     * inputs has (TAM/2 + 1) * 2 length.
     * inputs[i] are from put iff i belongs to {0..MAX/2}
     * inputs[i] are from put iff i belongs to {MAX/2 + 1..MAX}
     */
    Guard[] inputs = new Guard[MAX];
    for (int n = 0; n < MAX/2; n++) {
      inputs[n] = chPut[n].in();
      inputs[n + MAX/2] = chGet[n].in();
    }

    final Alternative services = new Alternative(inputs);
    int chosenService = 0;
    ChannelOutput cresp;
    Object[] items;

    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean[] syncCond = new boolean[MAX];
    while (true) {

      // synchronization conditions updated
      for (int n = 0; n < MAX/2; n++) {
        syncCond[n] = cprePut(n+1);
        syncCond[n + MAX/2] = cpreGet(n+1);
      }  
      /*@ assume (\forall int i; i > = 0 i < syncCond.length; 
        @           ( i < MAX_DATA && syncCond[i] ==> cprePut(i+1))
        @         ||
        @           ( i >= MAX_DATA && syncCond[i] ==> cpreGet(i+1))
        @        )
        @*/
      
      chosenService = services.fairSelect(syncCond);
      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0;
      //@ assume syncCond[chosenService];

      if (chosenService < MAX/2) {// put
        //@ assume cprePut(choice +1);
        items = (Object[]) chPut[chosenService].in().read();
        this.innerPut(items);
      } else {// get
        //@ assume cprePut(choice - MAX_DATA + 1);
        cresp = (ChannelOutput) chGet[chosenService - MAX/2].in().read();
        int lastItem = chosenService - MAX/2 + 1;
        cresp.write(this.innerGet(lastItem));
      }
    }
  }
  
  private void innerPut(Object[] items){
    for (Object item : items) {
      buffer[(first + nData) % MAX] = item;
      nData++;
    }
  }
  
  private Object[] innerGet(int n){
    Object[] items = new Object[n];
    for (int k = 0; k < n; k++) {
      items[k] = buffer[first];
      buffer[first] = null;
      first++;
      first %= MAX;
    }
    nData-= n ;
    return items;
  }

}
