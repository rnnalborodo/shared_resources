package es.upm.babel.ccjml.samples.warehouse.java.key;


public class WeightedCondition{

  /*@ public invariant weight >= 0 && 
    @                  weight <= WarehouseAccessControlMonitorBestOptKey.MAX_WEIGHT_IN_WAREHOUSE;
    @*/
  private /*@spec_public @*/int weight = 0;

  //@ public invariant weight >=0 ;
  private /*@spec_public @*/int condition;

  
  public WeightedCondition(int condition, int w) { 
    this.condition = condition; 
    this.weight = w;
  }
  public WeightedCondition(int condition) { 
    this.condition = condition; 
  }

  public int getWeight() {
    return weight;
  }

  public void setWeight(int weight) {
    this.weight = weight;
  }

  public int getCondition() {
    return condition;
  }

  public void signalCondition() {
    condition -- ;
  }

}
