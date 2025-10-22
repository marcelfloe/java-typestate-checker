package jatyc.key.contracts;

import java.util.HashMap;

/**
 * This class logs all given MethodInformation.
 */
public class ContractLog extends HashMap<MethodSignature, MethodInformation> {

  public void log(MethodInformation methodInformation) {
    this.put(methodInformation.signature(), methodInformation);
  }
}
