package es.upm.babel.ccjml.samples.bufferoddeven.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

/**
 * @author BABEL Group
 */
public class PutRequestCSP extends Tuple<Integer, One2OneChannel>{

  public PutRequestCSP(Integer fst, One2OneChannel snd) {
    super(fst, snd);
  }
  
  public One2OneChannel getChannel(){
    return super.getSnd();
  }

}
