import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper2 {

  private @Nullable JavaIterator iterator = null;

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public void init(@Requires("HasNext") JavaIterator it) {

  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Null)
    // :: warning: (this.iterator: Bottom)
    // :: error: (Cannot call [hasNext] on null (found: Null))
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: Bottom)
    return iterator.next();
  }

}

