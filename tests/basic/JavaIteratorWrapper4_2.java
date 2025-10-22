import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4_2 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext} | State{JavaIterator, end})
    // :: error: (Cannot call [hasNext] on State{JavaIterator, HasNext} | State{JavaIterator, end})
    if (iterator.hasNext()) {
      // :: warning: (this.iterator: State{JavaIterator, Next})
      return iterator.next();
    }
    return "";
  }

}
