package es.upm.babel.ccjml.samples.recyclingplant.java;

import org.jcsp.lang.Any2OneChannel;

/**
 * @author rnnalborodo
 */
public class NotifyWeightRequestCSP {
  private Any2OneChannel ch;

  public NotifyWeightRequestCSP(Any2OneChannel snd) {
    ch = snd;
  }
  
  public Any2OneChannel getChannel() {
    return ch;
  }

  public void setChannel(Any2OneChannel snd) {
    this.ch = snd;
  }
  
}
