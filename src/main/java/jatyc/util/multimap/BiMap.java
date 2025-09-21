package jatyc.util.multimap;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class BiMap<A,B> {
  private final Map<A, Set<Entry<A,B>>> aMap = new HashMap<>();
  private final Map<B, Set<Entry<A,B>>> bMap = new HashMap<>();
  private final Set<A> as = new HashSet<>();
  private final Set<B> bs = new HashSet<>();

  public BiMap() {}

  public void putA(A value) {
    as.add(value);
    aMap.put(value, new HashSet<>());
  }

  public void putB(B value) {
    bs.add(value);
    bMap.put(value, new HashSet<>());
  }

  public void map(A a, B b) {
    if (!as.contains(a)) {
      putA(a);
    }
    if (!bs.contains(b)) {
      putB(b);
    }
    Entry<A,B> entry = new Entry<>(a,b);
    aMap.get(a).add(entry);
    bMap.get(b).add(entry);
  }

  public Set<Entry<A,B>> getAMapping(A a) {
    return aMap.get(a);
  }

  public Set<Entry<A,B>> getBMapping(B b) {
    return bMap.get(b);
  }

  private record Entry<Y,Z> (Y y, Z z) {}
}
