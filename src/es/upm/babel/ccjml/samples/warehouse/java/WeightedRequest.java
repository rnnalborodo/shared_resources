package es.upm.babel.ccjml.samples.warehouse.java;

public class WeightedRequest {
  
  private int weight;
  private int warehouse;
  
  public WeightedRequest(int warehouse, int weight) {
    this.weight = weight;
    this.warehouse = warehouse;
  }
  public int getWeight() {
    return weight;
  }
  public void setWeight(int weight) {
    this.weight = weight;
  }
  public int getWarehouse() {
    return warehouse;
  }
  public void setWarehouse(int warehouse) {
    this.warehouse = warehouse;
  }
  @Override
  public String toString() {
    return "("+warehouse+":"+weight+")";
  }
  

}
