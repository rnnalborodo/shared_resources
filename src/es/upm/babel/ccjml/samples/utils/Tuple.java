package es.upm.babel.ccjml.samples.utils;

/**
 * Class that represents a pair of values. I do not like <p> Pair</p> class
 * 
 * @author raul.alborodo
 */

public class Tuple <TypeX, TypeY>{
  
  protected /*@ spec_public @*/ TypeX fst;
  protected /*@ spec_public @*/ TypeY snd;

  public Tuple(TypeX fst, TypeY snd) {
    this.fst = fst;
    this.snd = snd;
  }

  /*@ public normal_behaviour
    @   ensures \result == fst;
    @*/
  public /*@ pure @*/ TypeX getFst() {
    return fst;
  }

  /*@ public normal_behaviour
    @   assignable fst;
    @   ensures fst == obk;
    @*/
  public void setFst(TypeX obk) {
    this.fst = obk;
  }

  /*@ public normal_behaviour
    @   ensures \result == snd;
    @*/
  public /*@ pure @*/ TypeY getSnd() {
    return snd;
  }

  /*@ public normal_behaviour
    @   assignable snd;
    @   ensures snd == obj;
    @*/
  public void setSnd(TypeY obj) {
    this.snd = obj;
  }
}
