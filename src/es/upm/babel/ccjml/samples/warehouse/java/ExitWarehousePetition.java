package es.upm.babel.ccjml.samples.warehouse.java;

import org.jcsp.lang.One2OneChannel;

public class ExitWarehousePetition {
  
  private int warehouse;
  private One2OneChannel ch;
  
  public ExitWarehousePetition(int warehouse,
                           One2OneChannel ch) {
    super();
    this.warehouse = warehouse;
    this.ch = ch;
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
}
