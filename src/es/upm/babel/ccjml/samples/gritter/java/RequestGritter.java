package es.upm.babel.ccjml.samples.gritter.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

public class RequestGritter<T, U> extends Tuple<One2OneChannel,T> {
  
  U trd;
  
  public RequestGritter(One2OneChannel _pid, T _eid, U _a) {
    super(_pid, _eid);
    trd = _a;
  }
  
  public One2OneChannel getChannel(){
    return fst;
  }

  public T getSecond(){
    return snd;
  }
  
  public U getThird(){
    return trd;
  }
  
}
