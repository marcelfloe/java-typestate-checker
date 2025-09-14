import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapperWithGetter.protocol")
class JavaIteratorWrapper7 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, HasNext})
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, Next})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator} | State{JavaIterator, HasNext})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator} | State{JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, Next})
    // :: error: (Cannot call [next] on Shared{JavaIterator} | State{JavaIterator, Next})
    return iterator.next();
  }

  public @Ensures({"HasNext", "Next"}) JavaIterator getIterator() {
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, HasNext})
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, Next})
    // :: error: (Incompatible return value: cannot cast from Shared{JavaIterator} | State{JavaIterator, HasNext} to State{JavaIterator, HasNext})
    // :: error: (Incompatible return value: cannot cast from Shared{JavaIterator} | State{JavaIterator, Next} to State{JavaIterator, HasNext})
    return iterator;
  }

}
