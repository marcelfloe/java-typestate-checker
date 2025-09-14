import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper6 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: error: (Cannot call own public method [hasNext])
    hasNext();
    // :: warning: (this.iterator: Bottom)
    return iterator.hasNext();
  }

  public String next() {
    // :: error: (Cannot call own public method [hasNext])
    this.hasNext();
    // :: warning: (this.iterator: Bottom)
    return iterator.next();
  }

}
