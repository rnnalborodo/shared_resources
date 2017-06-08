package es.upm.babel.ccjml.samples.utils;

public class PreViolationSharedResourceException extends RuntimeException {

  private static final long serialVersionUID = -2282419737036152870L;
  
  public PreViolationSharedResourceException(String msg){
    super(msg);
   }

  public PreViolationSharedResourceException(){
    super("The PRE did NOT hold");
   }

}
