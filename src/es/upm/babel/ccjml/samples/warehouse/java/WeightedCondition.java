package es.upm.babel.ccjml.samples.warehouse.java;

import es.upm.babel.cclib.Monitor.Cond;

public class WeightedCondition implements Comparable<Object>{

  private int weight = 0;//
  private Cond condition;

  public WeightedCondition(Cond condition, int w) { 
    this.condition = condition; 
    this.weight = w;
  }
  public WeightedCondition(Cond condition) { 
    this.condition = condition; 
  }

  public int getWeight() {
    return weight;
  }

  public void setWeight(int weight) {
    this.weight = weight;
  }

  public Cond getCondition() {
    return condition;
  }

  //@Override
  public int compareTo(Object otra) {
    return this.peso - ((PetEntrar)otra).peso;
  }

}
