import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

@Typestate("CircularWithGetter")
class CircularObjWithGetter {

  private @Nullable CircularObjWithGetter f = null;

  public void setF(@Requires("State0") CircularObjWithGetter f) {
    // :: warning: (f: State{CircularObjWithGetter, State0})
    // :: warning: (this.f: State{CircularObjWithGetter, State0} | Null)
    // :: error: (The previous value of [this.f] did not complete its protocol (found: State{CircularObjWithGetter, State0} | Null))
    this.f = f;
  }

  public void finish() {
    // :: warning: (this.f: State{CircularObjWithGetter, State0} | Null)
    if (f != null) {
      // :: warning: (this.f: State{CircularObjWithGetter, State0})
      f.finish();
    }
  }

}
