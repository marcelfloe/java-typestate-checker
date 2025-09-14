import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapperPropagation {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: warning: (this.iterator: State{JavaIterator, Next} | State{JavaIterator, end})
    // :: error: (Cannot call [hasNext] on State{JavaIterator, Next} | State{JavaIterator, end})
    iterator.hasNext();
    return true;
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, Next} | State{JavaIterator, end})
    // :: error: (Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end})
    return iterator.next();
  }

}
