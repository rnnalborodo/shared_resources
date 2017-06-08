package es.upm.babel.ccjml.samples.airport.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

public class CSPRequest extends Tuple<One2OneChannel,Integer> {

  public CSPRequest(One2OneChannel fst, int snd) {
    super(fst, snd);
  }
  
  /*@ public normal_behaviour
    @   ensures \result == fst;
    @*/
  public /*@ pure @*/ One2OneChannel getChannel(){
    return this.getFst();
  }
  /*@ public normal_behaviour
    @   ensures \result == snd;
    @*/
  public /*@ pure @*/ int getRunway(){
    return this.getSnd().intValue();
  }
}
