import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    while (iterator.hasNext()) {
      // :: warning: (this.iterator: State{JavaIterator, Next})
      iterator.next();
    }
    return false;
  }

  public String next() {
    return iterator.next();
  }

}
