package jatyc.util.multimap;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * This class implements a map, which allows to get the set of all entries containing the value for values at any position inside the entry.
 * @param <A> the type of the value in the first position of an entry.
 * @param <B> the type of the value in the second position of an entry.
 * @param <C> the type of the value in the third position of an entry.
 */
public class TriMap <A,B,C> {
  private final Map<A, Set<Entry<A,B,C>>> aMap = new HashMap<>();
  private final Map<B, Set<Entry<A,B,C>>> bMap = new HashMap<>();
  private final Map<C, Set<Entry<A,B,C>>> cMap = new HashMap<>();
  private final Set<A> as = new HashSet<>();
  private final Set<B> bs = new HashSet<>();
  private final Set<C> cs = new HashSet<>();

  public TriMap() {}

  public void putA(A value) {
    as.add(value);
    aMap.put(value, new HashSet<>());
  }

  public void putB(B value) {
    bs.add(value);
    bMap.put(value, new HashSet<>());
  }

  public void putC(C value) {
    cs.add(value);
    cMap.put(value, new HashSet<>());
  }

  public void map(A a, B b, C c) {
    if (!as.contains(a)) {
      putA(a);
    }
    if (!bs.contains(b)) {
      putB(b);
    }
    if (!cs.contains(c)) {
      putC(c);
    }
    Entry<A,B,C> entry = new Entry<>(a,b,c);
    aMap.get(a).add(entry);
    bMap.get(b).add(entry);
    cMap.get(c).add(entry);
  }

  public Set<Entry<A,B,C>> getAMapping(A a) {
    return aMap.get(a);
  }

  public Set<Entry<A,B,C>> getBMapping(B b) {
    return bMap.get(b);
  }

  public Set<Entry<A,B,C>> getCMapping(C c) {
    return cMap.get(c);
  }

  private record Entry<X,Y,Z> (X x, Y y, Z z) {}
}
