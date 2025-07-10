public class ClientCode {

  /*@
    @ normal_behaviour
    @
    @ requires true;
    @
    @ ensures true;
    @
    @ assignable \nothing;
    @*/
  public static void example() {
    SUV suv = new SUV();
    //@ ghost String state = "OFF";
    while (!suv.turnOn()) {
      //@ set state = "OFF";
      //System.out.println("turning on...");
    }
    //@ set state = "COMFORT_ON";
    /*var1 = */suv.switchMode();
    // set state = suv.mode == Mode.SPORT ? "SPORT_ON" : "COMFORT_ON";
    // ^ not possible as suv.mode is private ^
    setSpeed(suv);
    //@ set state = "moved";
    //@ assert state.equals("moved");
  }

  /*@
    @ normal_behaviour
    @
    @ requires car != null;
    @
    @ ensures true;
    @
    @ assignable car;
    @*/
  private static void setSpeed(Car car) {
    if (car instanceof SUV && ((SUV) car).switchMode() == Mode.SPORT)
      ((SUV) car).setFourWheels(true);
    car.setSpeed(50);
    car.turnOff();
  }

  /*@
    @ normal_behaviour
    @
    @ requires true;
    @
    @ ensures true;
    @
    @ assignable \nothing;
    @*/
  public static void main(String[] args) {
    example();
    //System.out.println("Done!");
  }
}
