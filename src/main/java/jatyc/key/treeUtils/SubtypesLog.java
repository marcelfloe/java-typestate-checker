package jatyc.key.treeUtils;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

/**
 * This class stores the log of subtypes to each given type.
 */
public class SubtypesLog extends HashMap<String, Set<String>> {
  @Override
  public Set<String> get(Object key) {
    if (!this.containsKey(key) && key instanceof String) {
      this.put((String) key, new HashSet<>());
    }
    return super.get(key);
  }
}
