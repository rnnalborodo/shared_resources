package es.upm.babel.ccjml.samples.boundedbuffer.java;

import java.util.logging.Level;
import java.util.logging.Logger;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEvenSync;

/**
 * @author rnnalborodo
 */
public class BoundedBufferSync extends ABoundedBuffer implements BoundedBuffer{
  
  public BoundedBufferSync(){
    super(10);
  }
    
  public BoundedBufferSync(int a){
    super(a);
  }
  
  @Override
  public synchronized void put(int d) {
    while (!cprePut()) {
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(BufferOddEvenSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    }
    buffer[(first + nData) % MAX ] = d;
    nData++;
    notifyAll();
  }

  @Override
  public synchronized int get() {
    while (!cpreGet()) {
      try {
        wait();
      } catch (InterruptedException ex) {
        Logger.getLogger(BufferOddEvenSync.class.getName()).log(Level.SEVERE, null, ex);
      }
    }
    int d = buffer[first];
    first++;
    first %= MAX; 
    nData--;
    notifyAll();
    return d;
  }

}
