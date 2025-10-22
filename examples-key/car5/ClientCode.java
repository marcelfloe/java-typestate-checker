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
    Car car1 = new SUV();
    car1.turnOn();
    SUV suv = (SUV) car1;
    suv.switchMode();
    suv.setFourWheels(true);
    Car car2 = (Car) suv;
    car2.turnOff();
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
