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
    setSpeed(suv);
  }

  @JML("""
    requires \\invariant_for(suv);

    ensures true;

    assignable suv.*;
    """)
  private static void setSpeed(@Requires({"COMFORT_ON", "SPORT_ON"}) SUV suv) {
    if (suv.switchMode() == Mode.SPORT) suv.setFourWheels(true);
    suv.setSpeed(50);
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
