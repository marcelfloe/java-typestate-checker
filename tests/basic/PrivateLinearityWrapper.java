import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

// :: error: ([this.obj] did not complete its protocol (found: Shared{Linearity} | State{Linearity, ?}))
class PrivateLinearityWrapper {
  private Linearity obj = new Linearity();

  public void a() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Cannot call [a] on Shared{Linearity})
    obj.a();
  }

  public void b() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Cannot call [b] on Shared{Linearity})
    obj.b();
  }

  public Linearity get() {
    // :: warning: (this.obj: Shared{Linearity})
    return this.obj;
  }

  public void move1() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(this.obj);
  }

  public void move2() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(PrivateLinearityWrapper.this.obj);
  }

  public void move3() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(this.get());
  }

  public void move4() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(PrivateLinearityWrapper.this.get());
  }

  public static void use1(PrivateLinearityWrapper wrapper) {
    // :: warning: (wrapper: Shared{PrivateLinearityWrapper})
    // :: warning: (wrapper.obj: Unknown)
    // :: error: (Cannot access [wrapper.obj])
    LinearityTests.use(wrapper.obj);
  }

  public static void use2(PrivateLinearityWrapper wrapper) {
    // :: warning: (wrapper: Shared{PrivateLinearityWrapper})
    // :: warning: (wrapper.obj: Unknown)
    // :: error: (Cannot access [wrapper.obj])
    wrapper.obj.a();
  }
}
