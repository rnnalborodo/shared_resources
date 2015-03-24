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

public class ReadersWritersCSPDeferredRequest extends AReadersWriters implements CSProcess {

  /**
   *  Channel for receiving external request for each method
   */
  private final Any2OneChannel beforeWriteChannel = Channel.any2one();
  private final Any2OneChannel beforeReadChannel  = Channel.any2one();
  private final Any2OneChannel afterWriteChannel  = Channel.any2one();
  private final Any2OneChannel afterReadChannel   = Channel.any2one();

  /** 
   * List for enqueue all request for each method
   */
  private final Queue<Request<Object>> beforeWriteRequests = new LinkedList<>();
  private final Queue<Request<Object>> beforeReadRequests = new LinkedList<>();
  private final Queue<Request<Object>> afterWriteRequests = new LinkedList<>();
  private final Queue<Request<Object>> afterReadRequests = new LinkedList<>();
  
  private final Object token = new Object();
  
  public ReadersWritersCSPDeferredRequest() {}
  
  // API for this resource
  @Override
  public void beforeWrite() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    beforeWriteChannel.out().write(
                          new Request<Object>(innerChannel,token));
    innerChannel.in().read();
  }

  @Override
  public void afterWrite() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    afterWriteChannel.out().write(
                          new Request<Object>(innerChannel,token));
    innerChannel.in().read();
  }

  @Override
  public void beforeRead() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    beforeReadChannel.out().write(
                          new Request<Object>(innerChannel,token));
    innerChannel.in().read();
  }

  @Override
  public void afterRead() {
    //@ assume true
    One2OneChannel innerChannel = Channel.one2one();
    afterReadChannel.out().write(
                          new Request<Object>(innerChannel,token));
    innerChannel.in().read();
  }

  // SERVER SIDE CODE
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
      beforeWriteChannel.in(),
      beforeReadChannel.in(),
      afterWriteChannel.in(),
      afterReadChannel.in()
    };
    
    final Alternative services = new Alternative(guards);
    int chosenService = 0;
    while (true) {
      chosenService = services.fairSelect();
      //@ assume chosenService < guards.length && chosenService >= 0;
      //@ assume guards[chosenService].pending() > 0;
      
      switch(chosenService){
        //@ assume sinchCond{chosenService];
  
        case BEFORE_WRITE:
          //@ assert true;
          beforeWriteRequests.offer((Request<Object>)beforeWriteChannel.in().read());
          break;
          
        case BEFORE_READ:
          //@ assert true;
          beforeReadRequests.offer((Request<Object>)beforeReadChannel.in().read());
          break;
 
        case AFTER_WRITE: 
          //@ assert true;
          afterWriteRequests.offer((Request<Object>)afterWriteChannel.in().read());
          break;

        case AFTER_READ:
          //@ assert true;
          afterReadRequests.offer((Request<Object>)afterReadChannel.in().read());
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
            request.getChannel().out().write(token);
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
            request.getChannel().out().write(token);
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
            request.getChannel().out().write(token);
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
            request.getChannel().out().write(token);
            requestProcessed = true; 
//          } else {
//            break;
          }
        }
        //@ ensures $there$ $is$ $no$ $stored$ $thread$ $in$ $any$ $request$ $list$ $which$ $its$ $synchronization$ $condition$ $holds$
      }
    } // end while
  } // end run

  //@ ensures readers ==\old(readers) + 1;
  protected void innerBeforeRead(){
    readers++;
  }
  
  //@ ensures readers ==\old(readers) - 1;
  protected void innerAfterRead(){
    readers--;
  }
  
  //@ ensures writers ==\old(writers) + 1;
  protected void innerBeforeWrite(){
    writers++;
  }
  
  //@ ensures writers ==\old(writers) - 1;
  protected void innerAfterWrite(){
    writers--;
  }
  
  @Override
  public String toString(){
    return super.toString()+ 
        " - ["+
            "bR = "+ beforeReadRequests.size() + " | " +
            "aR = "+ afterReadRequests.size() + " | " +
            "bW = "+ beforeWriteRequests.size() + " | " +
            "aW = "+ afterWriteRequests.size() +"]";
  }
  
}
