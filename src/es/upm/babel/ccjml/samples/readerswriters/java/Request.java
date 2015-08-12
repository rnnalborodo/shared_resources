package es.upm.babel.ccjml.samples.readerswriters.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

public class Request< T extends Object > extends Tuple<One2OneChannel,T> {

  public Request(One2OneChannel fst, T snd) {
    super(fst, snd);
  }
  
  public One2OneChannel getChannel(){
    return fst;
  }

  public T getFootprint(){
    return snd;
  }
}
