import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper9 {

  private @Nullable JavaIterator iterator = null;

  // :: error: (Type of parameter [this] is Shared{JavaIteratorWrapper9}, expected State{JavaIteratorWrapper9, ?}})
  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
    JavaIteratorWrapper9 wrapper = this;
    // :: warning: (wrapper: State{JavaIteratorWrapper9, ?})
    // :: error: (Incompatible parameter: cannot cast from State{JavaIteratorWrapper9, ?} to Shared{JavaIteratorWrapper9})
    use(wrapper);
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Bottom)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: Bottom)
    return iterator.next();
  }

  public static void use(JavaIteratorWrapper9 it) {

  }

}
