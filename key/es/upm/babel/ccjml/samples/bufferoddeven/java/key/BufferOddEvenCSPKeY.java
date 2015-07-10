package es.upm.babel.ccjml.samples.bufferoddeven.java.key;

public class BufferOddEvenCSPKeY {

  //@ requires (syncCond.length == guards.length);
  /*@ ensures (\result >= 0 && \result < syncCond.length && 
    @          syncCond[\result] && guards[\result] > 0 )
    @         ||
    @         (\result == -1 &&
    @           (\forall int i; i >= 0 && i < syncCond.length; 
    @                           !syncCond[i] || guards[i] == 0)
    @         );
    @*/
  public static int /*@ pure @*/ fairSelect(int[] guards, boolean[] syncCond){
    for(int i = 0 ; i < syncCond.length; i++){
      if (syncCond[i] && guards[i] > 0)
        return i;
    }
    return -1;
  }
  
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

  
  /** WRAPPER Implementation
   *
   *  For Every Channel, we create a list of elements representing the messages.
   *  The size of the list corresponds with the messages waiting in the channel.
   *  In this case, due to the operation CPRE do not depend on parameters, int 
   *  is enough.s 
   */  
  //@ public invariant chPut >=0;
  private int chPut;
  //@ public invariant chGetEven >=0;
  private int chGetEven;
  //@ public invariant chGetOdd >=0;
  private int chGetOdd;

  /** SERVER IMPLEMENTATION */
  private final int GET_EVEN = 0;
  private final int GET_ODD = 1;
  private final int PUT = 2;
  
  /** Auxiliary variables to express 'assume' constraints as verifiable by KeY */
  //  explain each of the and why is that generally
  // safety
  private boolean wellFormedGuards;
  private boolean wellFormedSyncCond;
  private boolean propEffectiveFairSelect;
  private boolean propSafeSelection;
  /*@ requires chGetEven +
    @          chGetOdd +
    @          chPut > 0;
    @*/
  /*@ requires chGetEven +
    @          chGetOdd +
    @          chPut <= 2;
    @*/
  //@ assignable wellFormedGuards, wellFormedSyncCond, propEffectiveFairSelect;
  //@ assignable propSafeSelection;
  //@ ensures wellFormedGuards && wellFormedSyncCond;
  //@ ensures propEffectiveFairSelect;
  //@ ensures propSafeSelection;
  public void serverInstance(){
    /* 
     * One entry for each associated predicated. 
     * Union of all channel lists.
     */
    int[] guards = {
        chGetEven, 
        chGetOdd, 
        chPut
    };
    
    /**
     *  Conditional reception for fairSelect().
     *  Should be refreshed every iteration.
     */
    boolean[] syncCond = new boolean[3];
    
    int chosenService = 0;
    while (chosenService != -1) {
      syncCond[GET_EVEN] = cpreGet(EVEN);
      syncCond[GET_ODD] = cpreGet(ODD) ;
      syncCond[PUT] = nData < MAX;
      
      chosenService = fairSelect(guards, syncCond);
      propEffectiveFairSelect &= 
          chosenService < guards.length && chosenService >= 0 &&
          guards[chosenService] > 0 &&
          syncCond[chosenService];

      switch (chosenService){
        case GET_EVEN:
          //@ assume cpreGet(Type.EVEN);
          propSafeSelection &= cpreGet(EVEN);
//          int res = buffer[first];
          first ++;
          first%=MAX;
          nData--;
//          return res;
          guards[GET_EVEN]--;
          break;
        case GET_ODD:
          //@ assume cpreGet(Type.ODD);
          propSafeSelection &= cpreGet(ODD);
//        int res = buffer[first];
          first ++;
          first%=MAX;
          nData--;
//        return res;
          guards[GET_ODD]--;
          break;
        case PUT:
          propSafeSelection &= cprePut();
          //@ assume cprePut();
//          buffer[(first +nData)%MAX] = d;
          nData++;
          guards[PUT]--;
      }
    }// FIN BUCLE SERVICIO
  }// FIN SERVIDOR
  
}
