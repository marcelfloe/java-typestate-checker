import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

class MoveToConstructor2 extends MoveToConstructor {
  public MoveToConstructor2(@Requires({"State0", "State1"}) Linearity obj) {
    // :: warning: (obj: State{Linearity, State0} | State{Linearity, State1})
    super(obj);
    // :: warning: (obj: Shared{Linearity})
    // :: error: (Cannot call [finish] on Shared{Linearity})
    obj.finish();
  }
}
