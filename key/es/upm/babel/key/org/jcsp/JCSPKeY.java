package es.upm.babel.key.org.jcsp;

public class JCSPKeY {

  /*@ public normal_behaviour
    @ requires syncCond.length > 0 && guards.length > 0 && guards.length == syncCond.length;
    @ requires (\forall int i ; i >= 0 && i < guards.length; guards[i] >= 0);
    @ ensures (\result == -1 && 
    @              (\forall int j; j >= 0 && j < syncCond.length; (!syncCond[j] || guards[j] == 0)))
    @         || 
    @         (\result >= 0 && \result < syncCond.length && syncCond[\result] && guards[\result] > 0);
    @*/
  public static /*@pure @*/ int  fairSelect(boolean[] syncCond, int[] guards){
    int last = -1;
    /*@ loop_invariant 
      @    i >= 0 && i <= syncCond.length && 
      @    ( 
      @      (last == -1 && (\forall int j; j >= 0 && j < i ; (!syncCond[j] || guards[j] == 0))) ||
      @      (last >= 0 && last < syncCond.length && syncCond[last] && guards[last] > 0)
      @    );
      @ assignable last;
      @ decreases syncCond.length - i;
      @*/
    for (int i = 0; i < syncCond.length ; i++ ) {
      if(syncCond[i] && guards[i] > 0){
        last = i;
        break;
      }
    }
    return last;
  }

}
