package es.upm.babel.ccjml.samples.readerswriters.java;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;

/**
 * Readers-Writers implementation using JCSP Library with channel expansion.
 *
 * @author BABEL Group
 */
public class ReadersWritersCSP extends AReadersWriters implements CSProcess {
  
  /** WRAPPER IMPLEMENTATION */
  /**
   *  Channel for receiving external request for each method
   */
  private final Any2OneChannel ch_beforeWrite = Channel.any2one();
  private final Any2OneChannel ch_beforeRead  = Channel.any2one();
  private final Any2OneChannel ch_afterWrite  = Channel.any2one();
  private final Any2OneChannel ch_afterRead   = Channel.any2one();
  
  public ReadersWritersCSP() {}

  @Override
  public void beforeWrite() {
    //@ assume true;
    ch_beforeWrite.out().write(null);
  }

  @Override
  public void afterWrite() {
    //@ assume writers == 1;
    ch_afterWrite.out().write(null);
  }

  @Override
  public void beforeRead() {
    //@ assume true;
    ch_beforeRead.out().write(null);
  }

  @Override
  public void afterRead() {
    //@ assert readers > 0;
    ch_afterRead.out().write(null);
  }

  /** SERVER IMPLEMENTATION */
  /**
   * Constants representing the method presented in the API
   */
  private static final int BEFORE_WRITE = 0;
  private static final int BEFORE_READ = 1;
  private static final int AFTER_WRITE = 2;
  private static final int AFTER_READ = 3;

  @Override
  public void run() {
    
    /** One entry for each method */
    Guard[] guards = {
      ch_beforeWrite.in(),
      ch_beforeRead.in(),
      ch_afterWrite.in(),
      ch_afterRead.in()
    };
    
    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean syncCond[] = new boolean[4];
    
    Alternative services = new Alternative(guards);
    int chosenService = 0;
    while (true) {
      syncCond[BEFORE_WRITE] = (readers + writers == 0);
      syncCond[BEFORE_READ] = writers == 0;
      syncCond[AFTER_WRITE] = true;
      syncCond[AFTER_READ] = true;
      //@ assert syncCond is consistent,i.e, all refreshments are done properly
      
      chosenService = services.fairSelect(syncCond);
      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0;
      //@ assume syncCond[chosenService];
      
      switch(chosenService){
        case BEFORE_WRITE:
          //@ assert cpreBeforeWrite();
          ch_beforeWrite.in().read();
          innerBeforeWrite();
          break;

        case BEFORE_READ:
          //@ assert cpreBeforeWrite();
          ch_beforeRead.in().read();
          innerBeforeRead();
          break;
  
        case AFTER_WRITE: 
          //@ assert true;
          ch_afterWrite.in().read();
          innerAfterWrite(); 
          break;

        case AFTER_READ:
          //@ assert true;
          ch_afterRead.in().read();
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
}
