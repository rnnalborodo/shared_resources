package es.upm.babel.ccjml.samples.gritter.java;

public class Pair<T> {
  
  protected T siguiendo;
  protected boolean regrito;
  
  public Pair(T siguiendo, boolean regrito) {
    super();
    this.siguiendo = siguiendo;
    this.regrito = regrito;
  }

  public T estaSiguiendo() {
    return siguiendo;
  }

  public void setSiguiendo(T siguiendo) {
    this.siguiendo = siguiendo;
  }

  public boolean leeRegritos() {
    return regrito;
  }

  public void setRegrito(boolean regrito) {
    this.regrito = regrito;
  }
  
}
