import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper5 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    use(iterator);
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Shared{JavaIterator})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
    // :: warning: (this.iterator: Bottom)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: Bottom)
    return iterator.next();
  }

  public static void use(@Requires("HasNext") JavaIterator it) {
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

}
