package es.upm.babel.ccjml.samples.warehouse.java.key;

public class WeightedCondition{

  /*@ public invariant weight >= 0 && 
    @   weight <= WarehouseAccessControlMonitorBestOptKey.MAX_WEIGHT_IN_WAREHOUSE;
    @*/
  private /*@spec_public @*/int weight = 0;

  //@ public invariant condition >= 0;
  private /*@spec_public @*/int condition;

  public WeightedCondition(){
    this.weight = 0;
    this.condition = 0;
  }

  //@ ensures \result == weight;
  //@ ensures \result >= 0 && \result <= WarehouseAccessControlMonitorBestOptKey.MAX_WEIGHT_IN_WAREHOUSE;
  public int getWeight() {
    return weight;
  }

  /*@ public normal_behaviour
    @ requires w >= 0 && 
    @          w <= WarehouseAccessControlMonitorBestOptKey.MAX_WEIGHT_IN_WAREHOUSE ;
    @ assignable weight;
    @ ensures weight == w;
    @*/
  public void setWeight(int w) {
    this.weight = w;
  }

  //@ ensures \result == condition && \result >= 0;
  public int getCondition() {
    return condition;
  }
  
  //@ requires condition > 0;
  //@ assignable condition;
  //@ ensures \old(condition) == condition + 1;
  public void signalCondition() {
    condition -- ;
  }

}
