package es.upm.babel.ccjml.samples.utils;

/**
 * @author rnnalborodo
 */
public class Tuple <TX, TY>{

  protected TX fst;
  protected TY snd;

  public Tuple(TX fst, TY snd) {
    this.fst = fst;
    this.snd = snd;
  }

  public TX getFst() {
    return fst;
  }

  public void setFst(TX fst) {
    this.fst = fst;
  }

  public TY getSnd() {
    return snd;
  }

  public void setSnd(TY snd) {
    this.snd = snd;
  }
}
