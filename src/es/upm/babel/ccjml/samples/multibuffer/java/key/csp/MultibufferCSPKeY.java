package es.upm.babel.ccjml.samples.multibuffer.java.key.csp;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.AltingChannelInput;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelOutput;
import org.jcsp.lang.One2OneChannel;
import org.jcsp.lang.ProcessInterruptedException;

public class MultibufferCSPKeY{

  private final Any2OneChannel[] chPut;
  private final Any2OneChannel[] chGet;

  private int MAX_DATA;
  /* @ private represents maxData <- MAX_DATA; @ */
  
  private final Any2OneChannel chData[];

  private Object buffer[]; /* @ in data; @ */
  /*@ private represents
  @   data <- nData == 0
  @     ? JMLObjectSequence.EMPTY 
  @     : first + nData <= max   
  @     ? JMLObjectSequence.convertFrom(buffer).subsequence(first, first + nData - 1)
  @     : JMLObjectSequence.convertFrom(buffer).subsequence(first, maxData - 1).
  @     concat(JMLObjectSequence.convertFrom(buffer,(first + nData) % max - 1)); 
  @*/
  
  private int first;/* @ in data; @ */
  private int nData;/* @ in data; @ */

  public MultibufferCSPKeY() {
    this(10);
  }

  public MultibufferCSPKeY(int l) {
    this.MAX_DATA = l;
    chPut = new Any2OneChannel[MAX_DATA];
    chGet = new Any2OneChannel[MAX_DATA];

    for (int n = 0; n < MAX_DATA; n++) {
      chPut[n] = Channel.any2one();
      chGet[n] = Channel.any2one();
    }

    chData = new Any2OneChannel[MAX_DATA];
    buffer = new Object[MAX_DATA];

    first = 0;
    nData = 0;

  }

  /** 
    * WRAPPER IMPLEMENTATION
    */
  public void put(Object[] objs) {
//    System.out.println(Thread.currentThread().getId() + ") ++ PUT --> " + objs.length );
    chPut[objs.length - 1].out().write(objs);
//    System.out.println(Thread.currentThread().getId() + ") -- PUT --> " + objs.length );
  }

  public Object[] get(int n) {
    Object[] result;
    One2OneChannel chResp = Channel.one2one();

    System.out.println(Thread.currentThread().getId() + ") ++ GET --> " + n );
    
    chGet[n - 1].out().write(chResp.out());
    result = (Object[]) chResp.in().read();

    System.out.println(Thread.currentThread().getId() + ") -- GET --> "+ result.length );
    return result;
  }

  public boolean cprePut(int n) {
    return (MAX_DATA - nData) >= n;
  }

  public boolean cpreGet(int n) {
    return nData >= n;
  }

  // código del servidor
  public void run() {
    // DISPOSICIÓN DE LAS ENTRADAS PARA RECEPCIÓN ALTERNATIVA
    // tendremos un vector de entradas de tamaño (TAM/2 + 1) * 2
    // Las primeras TAM/2+1 entradas serán para las peticiones de
    // almacenar y las siguientes para las de extraer:
    // AltingChannelInput[] inputs = new AltingChannelInput[(TAM / 2 + 1) * 2];
    AltingChannelInput[] inputs = new AltingChannelInput[MAX_DATA * 2];

    Any2OneChannel uselessChannel = Channel.any2one();

    for (int n = 0; n < MAX_DATA; n++) {
      inputs[n] = chPut[n].in();
      inputs[n + MAX_DATA] = chGet[n].in();
    }

    Alternative servicios = new Alternative(inputs);
    int choice = 0, cuanto;
    ChannelOutput cresp;
    Object[] items;

    // RECEPCION CONDICIONAL
    boolean[] sincCond = new boolean[MAX_DATA * 2];
    while (true) {

      // refrescamos las condiciones (sin optimizar)
      for (int n = 0; n < MAX_DATA; n++) {
        // CPREs de almacenar
        sincCond[n] = cprePut(n+1);
        // CPREs de extraer
        sincCond[n + MAX_DATA] = cpreGet(n+1);
      }  
      
      choice = servicios.fairSelect();
      
      // System.out.println(choice);
      if (choice < MAX_DATA) {// put
        items = (Object[]) inputs[choice].read();
        for (Object item : items) {
          buffer[(first + nData) % MAX_DATA] = item;
          nData++;
        }
      } else {// get
        cresp = (ChannelOutput) inputs[choice].read();
        int lastItem = choice - MAX_DATA + 1;
        items = new Object[lastItem];
        for (int k = 0; k < lastItem; k++) {
          items[k] = buffer[first];
          buffer[first] = null;
          first++;
          first %= MAX_DATA;
        }
        nData-= lastItem ;
        cresp.write(items);
      }
    }// FIN BUCLE SERVICIO
  }// FIN SERVIDOR
}
