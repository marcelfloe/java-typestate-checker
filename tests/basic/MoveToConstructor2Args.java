import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

class MoveToConstructor2Args {
  // :: error: ([obj] did not complete its protocol (found: State{Linearity, State0} | State{Linearity, State1}))
  // :: error: ([obj2] did not complete its protocol (found: State{Linearity, State0} | State{Linearity, State1}))
  public MoveToConstructor2Args(
    @Requires({"State0", "State1"}) Linearity obj,
    @Requires({"State0", "State1"}) Linearity obj2
  ) {

  }
}
