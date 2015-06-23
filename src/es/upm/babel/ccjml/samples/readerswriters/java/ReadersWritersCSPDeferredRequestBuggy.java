package es.upm.babel.ccjml.samples.readerswriters.java;

import java.util.LinkedList;
import java.util.Queue;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;
import org.jcsp.lang.ProcessInterruptedException;

/**
 * Missing break statement in AFTER_WRITE switch condition.
 * 
 * @author BABEL Group
 *
 */
public class ReadersWritersCSPDeferredRequestBuggy extends AReadersWriters implements CSProcess {

  /** WRAPPER IMPLEMENTATION */
  /**
   *  Channel for receiving external request for each method
   */
  private final Any2OneChannel ch_beforeWrite = Channel.any2one();
  private final Any2OneChannel ch_beforeRead  = Channel.any2one();
  private final Any2OneChannel ch_afterWrite  = Channel.any2one();
  private final Any2OneChannel ch_afterRead   = Channel.any2one();

  /** 
   * List for enqueue all request for each method
   */
  private final Queue<Request<Object>> beforeWriteRequests = new LinkedList<>();
  private final Queue<Request<Object>> beforeReadRequests = new LinkedList<>();
  private final Queue<Request<Object>> afterWriteRequests = new LinkedList<>();
  private final Queue<Request<Object>> afterReadRequests = new LinkedList<>();
  
  public ReadersWritersCSPDeferredRequestBuggy() {}
  
  // API for this resource
  @Override
  public void beforeWrite() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    ch_beforeWrite.out().write( new Request<Object>(innerChannel,null));
    innerChannel.in().read();
  }

  @Override
  public void afterWrite() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    ch_afterWrite.out().write( new Request<Object>(innerChannel,null));
    innerChannel.in().read();
  }

  @Override
  public void beforeRead() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    ch_beforeRead.out().write( new Request<Object>(innerChannel,null));
    innerChannel.in().read();
  }

  @Override
  public void afterRead() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    ch_afterRead.out().write( new Request<Object>(innerChannel,null));
    innerChannel.in().read();
  }

  /** SERVER IMPLEMENTATION */
  /**
   * Constants representing the method presented in the API
   */
  private static final int BEFORE_WRITE = 0;
  private static final int BEFORE_READ = 1;
  private static final int AFTER_WRITE = 2;
  private static final int AFTER_READ = 3;

  @SuppressWarnings("unchecked")
  @Override
  public void run() {
    
    /** One entry for each method */
    Guard[] guards = {
      ch_beforeWrite.in(),
      ch_beforeRead.in(),
      ch_afterWrite.in(),
      ch_afterRead.in()
    };
    
    final Alternative services = new Alternative(guards);
    int chosenService = 0;
    while (true) {
      chosenService = services.fairSelect();
      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0;
      
      switch(chosenService){
  
        case BEFORE_WRITE:
          //@ assert true;
          beforeWriteRequests.offer((Request<Object>)ch_beforeWrite.in().read());
          break;
          
        case BEFORE_READ:
          //@ assert true;
          beforeReadRequests.offer((Request<Object>)ch_beforeRead.in().read());
          break;
 
        case AFTER_WRITE: 
          //@ assert true;
          afterWriteRequests.offer((Request<Object>)ch_afterWrite.in().read());


        case AFTER_READ:
          //@ assert true;
          afterReadRequests.offer((Request<Object>)ch_afterRead.in().read());
      }
      
      Request<Object> request;
      
      //unblocking code
      boolean requestProcessed = true;
      while (requestProcessed) {
        requestProcessed = false;
        int queueSize = beforeWriteRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (writers + readers == 0){
            //@ assume cpreBeforeWrite();
            request = beforeWriteRequests.poll();
            this.innerBeforeWrite(); 
            request.getChannel().out().write(null);
            requestProcessed = true; 
          } else {
            break;
          }
        }
        
        queueSize = beforeReadRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (writers == 0){
            //@ assume cprebeforeRead();
            request = beforeReadRequests.poll();
            this.innerBeforeRead(); 
            request.getChannel().out().write(null);
            requestProcessed = true; 
          }else {
            break;
          }
        }
        
        queueSize = afterWriteRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (true){
            //@ assume cpreAfterWrite();
            request =afterWriteRequests.poll();
            this.innerAfterWrite(); 
            request.getChannel().out().write(null);
            requestProcessed = true;
//          }else {
//            break;
          }
        }
        
        queueSize = afterReadRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (true){
            //@ assume cpreAfterRead();
            request =afterReadRequests.poll();
            this.innerAfterRead(); 
            request.getChannel().out().write(null);
            requestProcessed = true; 
//          } else {
//            break;
          }
        }
        //@ ensures (beforeReadRequest.size() > 0 ==> writers > 0)
        //@ ensures (afterReadRequest.size() > 0 ==> readers == 0)
        //@ ensures (beforeWriteRequest.size() > 0 ==> writers + readers > 0)
        //@ ensures (afterWriteRequest.size() > 0 ==> writers == 0)
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
