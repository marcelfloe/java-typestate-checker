package jatyc.key;

import java.util.HashMap;

public class ContractLog extends HashMap<MethodSignature, MethodInformation> {

  public void log(MethodInformation methodInformation) {
    this.put(methodInformation.signature(), methodInformation);
  }
}
