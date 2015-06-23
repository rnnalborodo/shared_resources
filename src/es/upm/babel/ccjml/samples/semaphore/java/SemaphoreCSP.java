 package es.upm.babel.ccjml.samples.semaphore.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.ChannelInput;
import org.jcsp.lang.Guard;
import org.jcsp.lang.ProcessInterruptedException;

/**
 * Semaphore implementation using JCSP Library.
 * 
 * @author rnnalborodo
 */
public class SemaphoreCSP implements Semaphore, CSProcess {
  
  private boolean value;
   //@ private represents sem <- value == 1;
  
  private final Any2OneChannel vChannel = Channel.any2one();
  private final Any2OneChannel pChannel = Channel.any2one();

  public SemaphoreCSP(){
    value = false;
  }

  @Override
  public void v() {
    vChannel.out().write(new vRequests());
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
      
      ChannelInput in;
      
      switch(choice){
        case V: 
          if (!value) {
            in = vChannel.in();
            in.read();
            innerV();
          }
          break;
  
        case P:
          if (value){
            in = pChannel.in();
            in.read();
            innerP();
          }
      }
    //  end{jml_clause:classServer}
    }
  }

  
  public void innerV() {
    value = true;
  }

  public void innerP(){
    value = false;
  }

}
