package es.upm.babel.ccjml.samples.multibuffer.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

/**
 * @author rnnalborodo
 */
public class GetRequestCSP extends Tuple<Integer, One2OneChannel>{

  public GetRequestCSP(Integer fst, One2OneChannel snd) {
    super(fst, snd);
  }

}
