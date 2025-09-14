import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper8 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
    // :: error: (Incompatible parameter: cannot cast from State{JavaIteratorWrapper8, ?} to State{JavaIteratorWrapper8, HasNext})
    use(this);
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Bottom)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: Bottom)
    return iterator.next();
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIteratorWrapper8, HasNext}))
  public static void use(@Requires("HasNext") JavaIteratorWrapper8 it) {

  }

}
