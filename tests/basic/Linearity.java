import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

@Typestate("Linearity.protocol")
class Linearity {

  public void a() {
  }

  public void b() {
  }

  public void finish() {
  }

  public void useOther(@Requires("State0") Linearity obj) {
    // :: warning: (obj: State{Linearity, State0})
    obj.a();
    // :: warning: (obj: State{Linearity, State1})
    obj.b();
  }

  private void moveThis1() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(this);
  }

  private void moveThis2() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(Linearity.this);
  }

}
