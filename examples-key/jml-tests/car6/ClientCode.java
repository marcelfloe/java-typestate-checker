import jatyc.lib.Requires;
import jatyc.lib.Typestate;
import jatyc.lib.JML;

public class ClientCode {

  @JML("""
    requires true;

    ensures true;

    assignable \\nothing;
    """)
  public static void example() {
    SUV suv = new SUV();
    suv.turnOn();
    suv.switchMode();
    suv.setFourWheels(false);
    suv.turnOff();
  }


  @JML("""
    requires true;

    ensures true;

    assignable \\nothing;
    """)
  public static void main(String[] args) {
    example();
  }
}
