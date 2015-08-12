package es.upm.babel.ccjml.samples.observer.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

public class Request<T> extends Tuple<One2OneChannel,T> {
  
  public Request(One2OneChannel _pid, T _eid) {
    super(_pid, _eid);
  }
  
  public One2OneChannel getChannel(){
    return fst;
  }

  public T getFootprint(){
    return snd;
  }
}
