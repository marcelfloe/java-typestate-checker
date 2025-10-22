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
    requires \\invariant_for(car);

    ensures true;

    assignable car.*;
    """)
  private static void setSpeed(@Requires("ON") Car car) {
    if (car instanceof SUV && ((SUV) car).switchMode() == Mode.SPORT)
      ((SUV) car).setFourWheels(true);
    car.setSpeed(50);
    car.turnOff();
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
