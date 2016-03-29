package es.upm.babel.ccjml.samples.warehouse.java;

import org.jcsp.lang.One2OneChannel;

public class EnterWarehousePetition implements Comparable<Object>{
  
  private int weight;
  private int warehouse;
  private One2OneChannel ch;
  
  public EnterWarehousePetition(int warehouse,
                           int weight, 
                           One2OneChannel ch) {
    super();
    this.weight = weight;
    this.warehouse = warehouse;
    this.ch = ch;
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
  
  public One2OneChannel getChannel() {
    return ch;
  }
  
  public void setChannel(One2OneChannel ch) {
    this.ch = ch;
  }
  
  public int compareTo(Object other) {
    return this.weight - ((EnterWarehousePetition)other).getWeight();
  }
  
}
