package es.upm.babel.ccjml.samples.warehouse.java.key;


public class WeightedCondition{

  /*@ public invariant weight >= 0 && 
    @   weight <= WarehouseAccessControlMonitorBestOptKey.MAX_WEIGHT_IN_WAREHOUSE;
    @*/
  private /*@spec_public @*/int weight = 0;

  //@ public invariant weight >=0 ;
  private /*@spec_public @*/int condition;

  //@ ensures \result == weight;
  public int getWeight() {
    return weight;
  }

  //@ assignable weight;
  //@ ensures this.weight == weight;
  public void setWeight(int weight) {
    this.weight = weight;
  }

  //@ ensures \result == condition;
  public int getCondition() {
    return condition;
  }
  
  //@ assignable condition;
  //@ ensures \old(condition) == condition + 1;
  public void signalCondition() {
    condition -- ;
  }

}
