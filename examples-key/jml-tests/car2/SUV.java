import jatyc.lib.Typestate;
import jatyc.lib.JML;

@Typestate("SUV")
public class SUV {
  private final int THRESHOLD = 80;

  private Mode mode;
  private boolean ecoDrive;
  private boolean fourWheels;
  private int speed;


  @JML("""
    requires_free Mode.COMFORT != null;

    ensures mode == Mode.COMFORT;
    ensures ecoDrive == false;
    ensures fourWheels == false;
    ensures speed == 0;

    assignable mode, ecoDrive, fourWheels, speed;
    """)
  public SUV() {
    this.mode = Mode.COMFORT;
    this.ecoDrive = false;
    this.fourWheels = false;
    this.speed = 0;
  }


  @JML("""
    requires_free Mode.COMFORT != null && Mode.SPORT != null && Mode.COMFORT != Mode.SPORT;
    requires_free mode == Mode.COMFORT || mode == Mode.SPORT;

    ensures ((\\old(mode) == Mode.SPORT)
    ==> (mode == Mode.COMFORT && !fourWheels))
    && ((\\old(mode) != Mode.SPORT)
    ==> (mode == Mode.SPORT && !ecoDrive))
    && \\result == mode;

    assignable mode, fourWheels, ecoDrive;
    """)
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


  @JML("""
    requires true;

    ensures ecoDrive == state;

    assignable ecoDrive;
    """)
  public void setEcoDrive(boolean state) {
    ecoDrive = state;
  }


  @JML("""
    requires true;

    ensures fourWheels == state;

    assignable fourWheels;
    """)
  public void setFourWheels(boolean state) {
    fourWheels = state;
  }


  @JML("""
    requires true;

    ensures ((ecoDrive && (b > THRESHOLD))
    ==> (speed == THRESHOLD));
    ensures ((!ecoDrive || (b <= THRESHOLD))
    ==> (speed == b));

    assignable speed;
    """)
  public void setSpeed(int b) {
    if(ecoDrive) {
      speed = b < THRESHOLD ? b : THRESHOLD;
    } else {
      speed = b;
    }
  }

  @JML("""
    requires true;
    ensures \\result == true;
    assignable \\nothing;
    """)
  public boolean turnOn() {
    return true;
  }

  @JML("""
    requires true;
    assignable \\nothing;
    """)
  public void turnOff() {}
}
