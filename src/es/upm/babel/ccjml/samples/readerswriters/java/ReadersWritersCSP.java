package es.upm.babel.ccjml.samples.readerswriters.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.ProcessInterruptedException;

public class ReadersWritersCSP extends AReadersWriters implements CSProcess {

  /**
   *  Channel for receiving external request for each method
   */
  private final Any2OneChannel beforeWriteChannel = Channel.any2one();
  private final Any2OneChannel beforeReadChannel  = Channel.any2one();
  private final Any2OneChannel afterWriteChannel  = Channel.any2one();
  private final Any2OneChannel afterReadChannel   = Channel.any2one();
  
  private final Object token = new Object();
//  
//  /**
//   * To express ND in state 00
//   */
//  private Random generator = new Random(System.currentTimeMillis());
  
  public ReadersWritersCSP() {}

  
  // API for this resource
  @Override
  public void beforeWrite() {
    //@ assume true
    beforeWriteChannel.out().write(token);
  }

  @Override
  public void afterWrite() {
    //@ assume true
    afterWriteChannel.out().write(token);
  }

  @Override
  public void beforeRead() {
    //@ assume true
    beforeReadChannel.out().write(token);
  }

  @Override
  public void afterRead() {
    //@ assert true;
    afterReadChannel.out().write(token);
  }

  // SERVER SIDE CODE
  /**
   * Constants representing the method presented in the API
   */
  private static final int BEFORE_WRITE = 0;
  private static final int BEFORE_READ = 1;
  private static final int AFTER_WRITE = 2;
  private static final int AFTER_READ = 3;

  //@ ensures sinchCond[0] ==> cpreBeforeWrite();
  //@ ensures sinchCond[1] ==> cpreBeforeRead();
  //@ ensures sinchCond[2] ==> true;
  //@ ensures sinchCond[3] ==> true;
  private void refreshSyncConditions(boolean[] synchCond) {
    synchCond[0] = (readers + writers == 0);
    synchCond[1] = writers == 0;
    //sinchCond[2] = true;
    //sinchCond[3] = true;
  }
  
  @Override
  public void run() {
    
    /** One entry for each method */
    Guard[] guards = {
      beforeWriteChannel.in(),
      beforeReadChannel.in(),
      afterWriteChannel.in(),
      afterReadChannel.in()
    };
    
    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     *  At the beginning
     */
    boolean syncCond[] = new boolean[4];
    refreshSyncConditions(syncCond);
    
    Alternative services = new Alternative(guards);
    int chosenService = 0;
    while (true) {
      
      refreshSyncConditions(syncCond);
      //@ assert syncCond is consistent,i.e, all refreshments are done properly
      
      try {
        chosenService = services.fairSelect(syncCond);
      } catch (ProcessInterruptedException e){}

      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0;
      //@ assume syncCond[chosenService];
      
      switch(chosenService){
        //@ assume sinchCond{chosenService];
  
        case BEFORE_WRITE:
          //@ assert cpreBeforeWrite();
          beforeWriteChannel.in().read();
          innerBeforeWrite();
          break;

        case BEFORE_READ:
          //@ assert cpreBeforeWrite();
          beforeReadChannel.in().read();
          innerBeforeRead();
          break;
  
        case AFTER_WRITE: 
          //@ assert true;
          afterWriteChannel.in().read();
          innerAfterWrite(); 
          break;

        case AFTER_READ:
          //@ assert true;
          afterReadChannel.in().read();
          innerAfterRead();
          break;
      }
    } // end while
  } // end run
  
  //@ requires true && cpreBeforeRead();
  //@ assignable readers ;
  //@ ensures readers == \old(readers) + 1;
  protected void innerBeforeRead(){
    readers++;
  }
  
  //@ requires readers > 0;
  //@ assignable readers ;
  //@ ensures readers == \old(readers) - 1;
  protected void innerAfterRead(){
    readers--;
  }
  
  //@ requires true && cpreBeforeWrite();
  //@ assignable writers ;
  //@ ensures writers == \old(writers) + 1;
  protected void innerBeforeWrite(){
    writers++;
  }
  
  //@ requires writers > 0;
  //@ assignable writers;
  //@ ensures writers == \old(writers) - 1;
  protected void innerAfterWrite(){
    writers--;
  }
  
  @Override
  public String toString(){
    return super.toString()+ 
        " - ["+
            "bR = "+ beforeReadChannel.in().pending() + " | " +
            "aR = "+ afterReadChannel.in().pending() + " | " +
            "bW = "+ beforeWriteChannel.in().pending() + " | " +
            "aW = "+ afterWriteChannel.in().pending() +"]";
  }
  
}
