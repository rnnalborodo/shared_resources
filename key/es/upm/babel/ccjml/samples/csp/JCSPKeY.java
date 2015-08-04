package es.upm.babel.ccjml.samples.csp;

public class JCSPKeY {
  
  //@ requires (syncCond.length == guards.length && guards.length > 0);
  //@ requires (syncCond.length <=2);
  /*@ ensures ((\result >= 0 && \result < syncCond.length) && 
    @          (syncCond[\result] && guards[\result] > 0 ))
    @       || (\result == -1 &&
    @         (\forall int i; i >= 0 && i < syncCond.length; 
    @                           !syncCond[i] || guards[i] == 0));
    @*/
  public static int /*@ pure @*/ fairSelect(boolean[] syncCond, int[] guards){
    /*@ maintaining 0<=i && i < syncCond.length
    @                && 
    @                 (\forall int j; 0 <= j && j<i;
    @                       !syncCond[i] || guards[i] == 0);
    @ assignable \nothing;
    @ decreasing syncCond.length-i;
    @*/
    for(int i = 0 ; i < syncCond.length; i++){
      if (syncCond[i] && guards[i] > 0){
        return i;
      }
    }
    return -1;
  }
}
