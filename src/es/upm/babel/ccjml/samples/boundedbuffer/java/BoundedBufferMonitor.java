package es.upm.babel.ccjml.samples.boundedbuffer.java;


import es.upm.babel.cclib.Monitor;
import es.upm.babel.cclib.Monitor.Cond;

/**
 * @author rnnalborodo
 */
public class BoundedBufferMonitor extends ABoundedBuffer implements BoundedBuffer {

  protected Monitor mutex;
  protected Cond getCond;
  protected Cond putCond;
  
  public BoundedBufferMonitor(){
    super(10);
  }
  
  public BoundedBufferMonitor(int m){
    super(m);
    
    mutex = new Monitor();
    getCond = mutex.newCond();
    putCond = mutex.newCond();
  }
  
  @Override
  public void put(int d) {
    mutex.enter();
    if (!cprePut()) {
      putCond.await();
    }
    
    //@ assume cprePut();
    
    buffer[(first + nData) % MAX ] = d;
    nData++;
    
    int signaled = 0;
    if (getCond.waiting() > 0) {
      getCond.signal();
      signaled++;
    } else if (putCond.waiting() > 0 && nData < MAX) {
      putCond.waiting();
      signaled ++;
    }
    
    //@ assert signaled == 0 || signaled == 1;
    
    mutex.leave();
  }

  @Override
  public  int get() {
    mutex.enter();
    
    if (!cpreGet()) {
      getCond.await();
    }
    
    //@ assume cpreGet();
    
    int d = buffer[first];
    first ++;
    first%=MAX;
    nData--;
    
    int signaled = 0;
    
    if (putCond.waiting()> 0) {
      putCond.signal();
    } else if (nData > 0 && getCond.waiting()> 0) {
      getCond.signal();
    } 
    
    //@ assert signaled == 0 || signaled == 1;
    
    mutex.leave();
    return d;
  }

}