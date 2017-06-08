package es.upm.babel.ccjml.samples.readerswriters.java;

import java.util.LinkedList;
import java.util.Queue;

import org.jcsp.lang.Alternative;
import org.jcsp.lang.Any2OneChannel;
import org.jcsp.lang.CSProcess;
import org.jcsp.lang.Channel;
import org.jcsp.lang.Guard;
import org.jcsp.lang.One2OneChannel;

public class ReadersWritersCSPDeferredRequest extends AReadersWriters implements CSProcess {

  /** WRAPPER IMPLEMENTATION */
  /**
   *  Channel for receiving external request for each method
   */
  private final Any2OneChannel chBeforeWrite = Channel.any2one();
  private final Any2OneChannel chBeforeRead  = Channel.any2one();
  private final Any2OneChannel chAfterWrite  = Channel.any2one();
  private final Any2OneChannel chAfterRead   = Channel.any2one();

  /** 
   * List for enqueue all request for each method
   */
  private final Queue<Request<Object>> beforeWriteRequests = new LinkedList<>();
  private final Queue<Request<Object>> beforeReadRequests = new LinkedList<>();
  private final Queue<Request<Object>> afterWriteRequests = new LinkedList<>();
  private final Queue<Request<Object>> afterReadRequests = new LinkedList<>();
  
  public ReadersWritersCSPDeferredRequest() {}
  
  // API for this resource
  @Override
  public void beforeWrite() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    chBeforeWrite.out().write( new Request<Object>(innerChannel,null));
    innerChannel.in().read();
  }

  @Override
  public void afterWrite() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    chAfterWrite.out().write( new Request<Object>(innerChannel,null));
    innerChannel.in().read();
  }

  @Override
  public void beforeRead() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    chBeforeRead.out().write( new Request<Object>(innerChannel,null));
    innerChannel.in().read();
  }

  @Override
  public void afterRead() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    chAfterRead.out().write( new Request<Object>(innerChannel,null));
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
      chBeforeWrite.in(),
      chBeforeRead.in(),
      chAfterWrite.in(),
      chAfterRead.in()
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
          beforeWriteRequests.offer((Request<Object>)chBeforeWrite.in().read());
          break;
          
        case BEFORE_READ:
          //@ assert true;
          beforeReadRequests.offer((Request<Object>)chBeforeRead.in().read());
          break;
 
        case AFTER_WRITE: 
          //@ assert writers == 1;
          afterWriteRequests.offer((Request<Object>)chAfterWrite.in().read());
          break;

        case AFTER_READ:
          //@ assert readers > 0;
          afterReadRequests.offer((Request<Object>)chAfterRead.in().read());
      }
      
      Request<Object> request;
      
      //unblocking code
      boolean requestProcessed = true;
      while (requestProcessed) {
        requestProcessed = false;
        int queueSize = beforeWriteRequests.size();
        for(int i = 0; i < queueSize;i++) {
          if (writers + readers == 0){
            //@ assert cpreBeforeWrite();
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
            //@ assert cprebeforeRead();
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
            //@ assert cpreAfterWrite();
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
            //@ assert cpreAfterRead();
            request =afterReadRequests.poll();
            this.innerAfterRead(); 
            request.getChannel().out().write(null);
            requestProcessed = true; 
//          } else {
//            break;
          }
        }
        //@ ensures (beforeReadRequests.size() > 0 ==> !writers == 0)
        //@ ensures (afterReadRequests.size() > 0 ==> !true)
        //@ ensures (beforeWriteRequests.size() > 0 ==> !writers + readers == 0)
        //@ ensures (afterWriteRequests.size() > 0 ==> !true)
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
