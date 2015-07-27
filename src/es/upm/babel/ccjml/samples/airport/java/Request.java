package es.upm.babel.ccjml.samples.airport.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

public class Request extends Tuple<One2OneChannel,Integer> {

  public Request(One2OneChannel fst, int snd) {
    super(fst, snd);
  }
  
  public One2OneChannel getChannel(){
    return fst;
  }

  public int getRunway(){
    return snd;
  }
}
