import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

// :: error: ([this.obj] did not complete its protocol (found: Shared{Linearity} | State{Linearity, ?}))
class PrivateLinearityWrapperNoMoves {
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
}
