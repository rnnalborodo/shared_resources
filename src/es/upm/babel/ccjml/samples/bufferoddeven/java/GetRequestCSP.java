package es.upm.babel.ccjml.samples.bufferoddeven.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.bufferoddeven.java.BufferOddEven.Type;
import es.upm.babel.ccjml.samples.utils.Tuple;

/**
 *
 * @author BABEL Group 
 */
public class GetRequestCSP extends Tuple<Type, One2OneChannel>{

  public GetRequestCSP(Type fst, One2OneChannel snd) {
    super(fst, snd);
  }

  public One2OneChannel getChannel(){
    return super.getSnd();
  }
  
  public Type getType(){
    return super.getFst();
  }
}
