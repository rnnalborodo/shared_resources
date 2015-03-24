 package es.upm.babel.ccjml.samples.boundedsemaphore.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.Guard;
import org.jcsp.lang.ProcessInterruptedException;

import es.upm.babel.ccjml.samples.semaphore.java.Semaphore;
import es.upm.babel.ccjml.samples.semaphore.java.pRequest;
import es.upm.babel.ccjml.samples.semaphore.java.vRequest;

/**
 * Semaphore implementation using JCSP Library.
 * 
 * @author rnnalborodo
 */
public class BoundedSemaphoreCSP implements BoundedSemaphore, CSProcess {
  
  private int value;
  private int bound;
  
  private final Any2OneChannel vChannel = Channel.any2one();
  private final Any2OneChannel pChannel = Channel.any2one();

  public BoundedSemaphoreCSP(int v){
    bound = v;
    value = 0;
  }

  //@ensures \result == value < bound;
  private boolean cpreV(){
    return value < bound;
  }
  
  //@ensures \result == value > 0;
  private boolean cpreP(){
    return value > 0;
  }
  
  @Override
  public void v() {
    vChannel.out().write(new vRequest());
  }
  
  @Override
  public void p() {
    pChannel.out().write(new pRequest());
  }

  //server side code
  private static final int V = 0;
  private static final int P = 1;
  
  @Override
  public void run() {
    Guard[] inputs = {
      vChannel.in(),
      pChannel.in()
    };
    Alternative services = new Alternative(inputs);
//    Alternative services = new Alternative({this.value, !this.value});
    int choice = 0;
    while (true) {
      try {
        choice = services.fairSelect();
      } catch (ProcessInterruptedException e){}

      switch(choice){
      case V: 
        if (cpreV()) {
          ChannelInput in = vChannel.in();
          in.read();
          innerV();
        }
        break;

      case P:
        if (cpreP()){
          ChannelInput input = pChannel.in();
          input.read();
          innerP();
        }
      }
    //  end{jml_clause:classServer}
    }
  }

  
  public void innerV() {
    value++;
  }

  public void innerP(){
    value--;
  }

}
