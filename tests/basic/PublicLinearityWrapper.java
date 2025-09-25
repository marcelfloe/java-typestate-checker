import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

// Enforce protocol completeness for objects inside other objects
// :: error: ([this.obj] did not complete its protocol (found: Shared{Linearity} | State{Linearity, ?}))
class PublicLinearityWrapper {
  public Linearity obj = new Linearity();

  public void setNull() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Cannot assign because [this.obj] is not accessible here)
    obj = null;
  }

  public void a() {
    // :: error: (Cannot call [a] on Shared{Linearity})
    // :: warning: (this.obj: Shared{Linearity})
    obj.a();
  }

  public void b() {
    // :: error: (Cannot call [b] on Shared{Linearity})
    // :: warning: (this.obj: Shared{Linearity})
    obj.b();
  }

  public Linearity get() {
    // :: warning: (this.obj: Shared{Linearity})
    return this.obj;
  }

  public void move1() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    // :: warning: (this.obj: Shared{Linearity})
    LinearityTests.use(this.obj);
  }

  public void move2() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    // :: warning: (this.obj: Shared{Linearity})
    LinearityTests.use(PublicLinearityWrapper.this.obj);
  }

  public void move3() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(this.get());
  }

  public void move4() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(PublicLinearityWrapper.this.get());
  }

  public static void use1(PublicLinearityWrapper wrapper) {
    // :: warning: (wrapper: Shared{PublicLinearityWrapper})
    // :: warning: (wrapper.obj: Unknown)
    // :: error: (Cannot access [wrapper.obj])
    LinearityTests.use(wrapper.obj);
  }

  public static void use2(PublicLinearityWrapper wrapper) {
    // :: warning: (wrapper: Shared{PublicLinearityWrapper})
    // :: warning: (wrapper.obj: Unknown)
    // :: error: (Cannot access [wrapper.obj])
    wrapper.obj.a();
  }
}
