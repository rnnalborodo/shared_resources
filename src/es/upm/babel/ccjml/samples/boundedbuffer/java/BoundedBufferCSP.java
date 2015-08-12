package es.upm.babel.ccjml.samples.boundedbuffer.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.AltingChannelInput;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelOutput;
import org.jcsp.lang.One2OneChannel;
import org.jcsp.lang.ProcessInterruptedException;

public class BoundedBufferCSP extends ABoundedBuffer implements BoundedBuffer, CSProcess {

  private final Any2OneChannel chPut;
  private final Any2OneChannel chGet;
  
  public BoundedBufferCSP(int m){
    super(m);
    
    chPut = Channel.any2one();
    chGet = Channel.any2one();   
  }
  
  @Override
  public void put(int d) {
    chPut.out().write(d);
  }

  @Override
  public int get() {
    One2OneChannel chResp = Channel.one2one();
    chGet.out().write(chResp.out());
    
    return (Integer)chResp.in().read();
  }
    
  private final int GET = 0;
  private final int PUT = 1;
  
  // código del servidor
  @Override
  public void run() {
    AltingChannelInput[] inputs = {
                                                        chGet.in(), 
                                                        chPut.in()
                                                    };
    Alternative services = new Alternative(inputs);
    int currentService = 0;
    ChannelOutput cresp;
    
    while (true) {
      try {
        currentService = services.fairSelect();
      } catch (ProcessInterruptedException e){}
      
      if (currentService == GET) {
        cresp =(ChannelOutput) chGet.in().read();
        int res = buffer[first];
        first ++;
        first%=MAX;
        nData--;
        cresp.write(res);
        
      } else { //put
        
        if (cprePut()){
          int d = (Integer) chPut.in().read();
          buffer[(first +nData)%MAX] = d;
          nData++;
          System.out.println(" put");
        }
        
      }
    }// FIN BUCLE SERVICIO
  }// FIN SERVIDOR
}
