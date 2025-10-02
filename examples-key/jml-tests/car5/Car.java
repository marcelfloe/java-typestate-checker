import jatyc.lib.Typestate;
import jatyc.lib.JML;

@Typestate("Car")
public class Car {

  public int speed;

  public Car() {}

  @JML("""
    requires true;
    ensures \\result == true;
    assignable \\nothing;
    """)
  public boolean turnOn() {return true;}

  @JML("""
    requires true;
    assignable \\nothing;
    """)
  public void setSpeed(int b) {}

  @JML("""
    requires true;
    assignable \\nothing;
    """)
  public void turnOff() {}
}
