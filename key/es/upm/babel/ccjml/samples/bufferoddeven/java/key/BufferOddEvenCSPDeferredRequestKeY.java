package es.upm.babel.ccjml.samples.bufferoddeven.java.key;

import es.upm.babel.ccjml.samples.csp.list.src.List;

public class BufferOddEvenCSPDeferredRequestKeY {

  /* INNER STATE */

  //public enum Type { EVEN, ODD }
  protected static final int EVEN = 1;
  protected static final int ODD = 0;

  // public invariant MAX == 3;
  public static final int MAX = 3;

  //@ public invariant 0 <= nData && nData <= MAX;
  private /*@ spec_public @*/ int nData;  
  //@ public invariant 0 <= first && first < MAX;
  private /*@ spec_public @*/ int first;
  //@ public invariant buffer.length == MAX; 
  private /*@spec_public@*/ int[] buffer;

  /*@ public normal_behaviour
    @  ensures \result == nData <= MAX - 1;
    @*/
  private boolean cprePut() {
    return nData <= MAX - 1;
  }

  /*@ public normal_behaviour
    @  requires t == EVEN || t == ODD;
    @  ensures \result == (nData > 0 
    @    && ((buffer[first] % 2 == 0 && t == EVEN) || 
    @        (buffer[first] % 2 == 1 && t == ODD))) ;
    @*/
  private boolean cpreGet(int t) {
    return nData > 0 
        && ((buffer[first] % 2 == 0 && t == EVEN) || 
            (buffer[first] % 2 == 1 && t == ODD));
  }

  /**
   *  For Every Channel, we create a int representing the ammount of requests.
   *  The size of the list corresponds with the messages waiting in the channel.
   */  
  private List putRequest;
  private List getRequest;

  /** SERVER IMPLEMENTATION */
  /** Auxiliary variables to express 'assume' constraints as verifiable by KeY */
  private boolean cprePreservation;
  private boolean effectiveness;

  //@ requires putRequest.size() + getRequest.size() >= 2;
  //@ assignable putRequest, getRequest;
  //@ assignable cprePreservation;
  //@ assignable buffer[*], first, nData;
  //@ ensures cprePreservation;
  //@ ensures effectiveness;
  public void processRequest() {
    cprePreservation = effectiveness = true;
    /**
     * Unblocking code
     * Must always process all request which is associated CPRE holds
     */
    boolean requestProcessed;
    int queueSize;
    do {
      requestProcessed = false;

      queueSize = putRequest.size();
      for(int i = 0; i < queueSize;i++) {
        if (nData < MAX){
          cprePreservation &= nData < MAX;

          int r = (int) getRequest.get(new Integer(0));
          putRequest.remove(r);

          buffer[(first +nData)%MAX] = r;
          nData++;
          requestProcessed = true; 
        } else {
          effectiveness &= !(nData < MAX);
          break;
        }
      }

      queueSize = getRequest.size();
      for(int i = 0; i < queueSize;i++) {
        if (nData > 0){
          int type = (int) getRequest.get(new Integer(0));
          getRequest.remove(type);
          if ( (buffer[first] % 2 == 0 && type == EVEN ) ||
              (buffer[first] % 2 == 1 && type == ODD )){
            cprePreservation &= cpreGet(type);
            //@ assume true && invariant && cpreGet(rq.getType());
//            int res = buffer[first];
            first ++;
            first%=MAX;
            nData--;
//            return res;
            requestProcessed = true;
          }  else {
            effectiveness &= !cpreGet(type); 
            getRequest.add(type);
          }
        } 
      }

    } while (requestProcessed);
  }// FIN SERVIDOR
}
