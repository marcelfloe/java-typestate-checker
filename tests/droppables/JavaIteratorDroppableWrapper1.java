import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorDroppableWrapper.protocol")
class JavaIteratorDroppableWrapper1 {

  private JavaIteratorDroppable iterator = new JavaIteratorDroppable();

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIteratorDroppable, HasNext})
    // :: warning: (this.iterator: State{JavaIteratorDroppable, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIteratorDroppable, Next})
    return iterator.next();
  }

}
