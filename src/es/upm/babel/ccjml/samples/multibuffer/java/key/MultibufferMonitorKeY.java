package es.upm.babel.ccjml.samples.multibuffer.java.key;

/**
 * @author rnnalborodo
 */
public class MultibufferMonitorKeY{
// Class members
  /*@ public invariant
    @  MAX == 1;
    */
  public static final int MAX = 1;

  // Instance members: shared resource internal state
  /*@ public invariant
    @  0 <= nData && nData <= MAX;
    @*/
  private /*@ spec_public @*/ int nData;  
  /*@ public invariant 0 <= first && first < MAX; @*/
  private /*@ spec_public @*/ int first;
  
  /*@ public invariant buffer.length == MAX; @*/
  private /*@spec_public@*/ int[] buffer;
  // ------------------------ concurrency instrumentation ------------------------

  /*@ public invariant
    @         emptiness.length == MAX+1 && 
    @         (\forall int i; i >= 0 && i < MAX+1 ; emptiness[i] >= 0);
    @*/
  // empty slots
  private final /*@ spec_public @*/int[] emptiness = new int[MAX+1];

  /*@ public invariant
    @         fullness.length == MAX+1 && 
    @         (\forall int i; i >= 0 && i < MAX+1; fullness[i] >= 0);
    @*/
  // data
  private final /*@ spec_public @*/int[] fullness = new int[MAX+1];

  // prop_0_1_signal depicted as an invariant
  /*@ public invariant
    @            signaled >= 0 && signaled <= 1;
    @*/
  private /*@ spec_public @*/int signaled  = 0;

  //@ requires n > 0 && n < MAX;
  //@ ensures \result != n > MAX - nData;
  private /*@ pure @*/ boolean  cprePut(int n){
    return MAX - nData >= n;
  }

  //@ requires n > 0 && n < MAX;
  //@ ensures \result != n > nData;
  private /*@ pure @*/ boolean cpreGet(int n){
    return nData >= n;
  }

  //@ assignable signaled, fullness[*], emptiness[*];
  //@ assignable first, buffer, nData;
  //prop_safe_signal
  /* ensures
     @  (\forall int i; i>=1 && i < MAX + 1; 
     @        (emptiness[i] + 1 == \old(emptiness)[i] ==> cprePut(i)) &&
     @        (fullness[i] + 1 == \old(fullness)[i] ==> cpreGet(i))
     @  );
     @*/
  // prop_signal_0_1
  /*@ ensures 
     @  (\forall int i; i>=1 && i < MAX + 1; 
     @    emptiness[i] == \old(emptiness[i]) && fullness[i] == \old(fullness[i]) )
     @  ||
     @  (\exists int i; i>=1 && i < MAX + 1;
     @          emptiness[i] + 1== \old(emptiness[i]) && fullness[i]==\old(fullness[i]) )
     @  ||
     @  (\exists int i; i>=1 && i < MAX + 1;
     @          fullness[i] + 1== \old(fullness[i]) && emptiness[i]==\old(emptiness[i])
     @  );
     @*/
  // prop_signal_effective
  /* ensures
     @  signaled == 1
     @  ==>
     @  (\exists int i; i>=1 && i < MAX + 1;
     @        emptiness[i] + 1 == \old(emptiness[i]) ||
     @        fullness[i] + 1 == \old(fullness[i])
     @  );
     @*/
  // prop_liveness
  /* ensures
     @  (\exists int i; i >= 1 && i < MAX + 1;
     @       \old(emptiness[i])> 0 && cprePut(i) ||
     @       \old(fullness[i])> 0 && cpreGet(i))
     @  ==>
     @    signaled == 1;
     @*/
  // prop_signal_and_return
  /* ensures 
     @  first == \old(first) && nData == \old(nData) &&
     @  buffer == \old(buffer) ;
     @*/
  private void unblobckingCode(){
    // Second step using Model Search as Aritmetic Treatment
    signaled = 0;
    // @ loop_invariant 0 < i && i <= MAX-nData; 
    for (int i = MAX-nData; i > 0 && signaled == 0; i--) {
      if (emptiness[i] > 0) {
        emptiness[i]--;
        //@ assert cprePut(i);
        signaled ++;
      }
    }
    //@ loop_invariant 0 < j && j <= nData; 
    for (int j = nData; j > 0 && signaled == 0 ; j--) {
      if (fullness[j] > 0) {
        fullness[j]--;
        //@ assert cpreGet(i);
        signaled++;
      } 
    }
  }
}
