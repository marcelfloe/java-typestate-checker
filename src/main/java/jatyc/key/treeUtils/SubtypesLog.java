package jatyc.key.treeUtils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class SubtypesLog extends HashMap<String, Set<String>> {
  @Override
  public Set<String> get(Object key) {
    if (!this.containsKey(key) && key instanceof String) {
      this.put((String) key, new HashSet<>());
    }
    return super.get(key);
  }
}
