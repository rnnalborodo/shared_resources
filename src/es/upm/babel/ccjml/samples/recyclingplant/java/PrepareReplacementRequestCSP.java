package es.upm.babel.ccjml.samples.recyclingplant.java;

import org.jcsp.lang.One2OneChannel;

import es.upm.babel.ccjml.samples.utils.Tuple;

/**
 * @author rnnalborodo
 */
public class PrepareReplacementRequestCSP extends Tuple<Integer, One2OneChannel>{

  public PrepareReplacementRequestCSP(Integer fst, One2OneChannel snd) {
    super(fst, snd);
  }
  
  public int getWeight() {
    return fst;
  }

  public void setWeight(int fst) {
    this.fst = fst;
  }

  public One2OneChannel getAuxChannel() {
    return snd;
  }

  public void setAuxChannel(One2OneChannel snd) {
    this.snd = snd;
  }
  
}
