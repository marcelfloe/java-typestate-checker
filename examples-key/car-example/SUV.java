
public class SUV extends Car {
  private final int THRESHOLD = 80;

  private Mode mode;
  private boolean ecoDrive;
  private boolean fourWheels;
  private int speed;

  /*@ public normal_behaviour
    @
    @ requires Mode.COMFORT != null;
    @
    @ ensures mode == Mode.COMFORT;
    @ ensures ecoDrive == false;
    @ ensures fourWheels == false;
    @ ensures speed == 0;
    @ ensures this != null;
    @
    @ assignable mode, ecoDrive, fourWheels, speed;
    @*/
  public SUV() {
    this.mode = Mode.COMFORT;
    this.ecoDrive = false;
    this.fourWheels = false;
    this.speed = 0;
  }

  /*@ public normal_behaviour
    @
    @ requires Mode.COMFORT != null && Mode.SPORT != null;
    @
    @ ensures ((\old(mode) == Mode.SPORT)
    @ ==> (mode == Mode.COMFORT && \result == Mode.COMFORT && !fourWheels))
    @ && ((\old(mode) != Mode.SPORT)
    @ ==> (mode == Mode.SPORT && \result == Mode.SPORT && !ecoDrive));
    @ ensures \result != null;
    @
    @ assignable mode, fourWheels, ecoDrive;
    @*/
  public Mode switchMode() {
    if (mode == Mode.SPORT) {
      mode = Mode.COMFORT;
      fourWheels = false;
    } else {
      mode = Mode.SPORT;
      ecoDrive = false;
    }
    return mode;
  }


  /*@ public normal_behaviour
    @
    @ requires true;
    @
    @ ensures ecoDrive == state;
    @
    @ assignable ecoDrive;
    @*/
  public void setEcoDrive(boolean state) {
    ecoDrive = state;
  }

  /*@ public normal_behaviour
    @
    @ requires true;
    @
    @ ensures fourWheels == state;
    @
    @ assignable fourWheels;
    @*/
  public void setFourWheels(boolean state) {
    fourWheels = state;
  }

  /*@ public normal_behaviour
    @
    @ requires true;
    @
    @ ensures ((ecoDrive && (b > THRESHOLD))
    @ ==> (speed == THRESHOLD));
    @ ensures ((!ecoDrive || (b <= THRESHOLD))
    @ ==> (speed == b));
    @
    @ assignable speed;
    @*/
  // Override
  public void setSpeed(int b) {
    //assert(ecoDrive); //-> no proof
    //assert(!ecoDrive); //-> no proof
    if(ecoDrive) {
      //assert(ecoDrive); //-> proof
      //assert(!ecoDrive); //-> no proof
      speed = b < THRESHOLD ? b : THRESHOLD;
    } else {
      //assert(ecoDrive); //-> no proof
      //assert(!ecoDrive); //-> proof
      speed = b;
    }
  }
}
