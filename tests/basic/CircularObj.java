import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

@Typestate("Circular")
class CircularObj {

  public @Nullable CircularObj f = null;

  public void finish() {

  }

}
