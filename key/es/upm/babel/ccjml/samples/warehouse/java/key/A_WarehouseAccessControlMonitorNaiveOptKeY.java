package es.upm.babel.ccjml.samples.warehouse.java.key;

public class A_WarehouseAccessControlMonitorBestOptKey {

  //@ ghost int awakenThread;

  //@ public invariant N_ROBOTS > 0;
  public static final int N_ROBOTS;
  //@ public invariant N_WAREHOUSE > 0;
  public static final int N_WAREHOUSE = 4;
  //@ public invariant MAX_WEIGHT_IN_WAREHOUSE > 0;
  public static final int MAX_WEIGHT_IN_WAREHOUSE = 10;
  
  // INNER STATE ATTRIBUTES
  //@ public invariant corridor.length == N_WAREHOUSE -1;
  private /*@ spec_public @*/ boolean corridor[];
  


  /* @
    @ public invariant enteringWarehouseZero.length == N_ROBOTS && 
    @   (\forall int i; i >= 1 && i < N_ROBOTS;
    @              enteringWarehouseZero[i-1]!= null && enteringWarehouseZero[i]!= null &&
    @              enteringWarehouseZero[i-1].getWeight() <= enteringWarehouseZero[i].getWeight() )
    @ ;
    @*/
  private /*@ spec_public @*/ WeightedCondition enteringWarehouseZero[];


}