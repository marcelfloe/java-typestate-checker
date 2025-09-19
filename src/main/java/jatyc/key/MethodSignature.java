package jatyc.key;

import java.util.List;

/**
 * This record models a method signature.
 * @param classType the class containing the method
 * @param methodName the name of the method
 * @param parameterTypes the types of the parameters of the method
 */

public record MethodSignature(String classType, String methodName, List<String> parameterTypes) {
  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof MethodSignature other)) return false;
    if (parameterTypes.size() != other.parameterTypes.size()) return false;
    for (int i = 0; i < parameterTypes.size(); i++) {
      if (!parameterTypes.get(i).equals(other.parameterTypes.get(i))) return false;
    }
    return methodName.equals(other.methodName) && classType.equals(other.classType);
  }

  @Override
  public int hashCode() {
    int hashCode = 0;
    for (String parameterType : parameterTypes) {
      hashCode += parameterType.hashCode();
    }
    return hashCode + methodName.hashCode() + classType.hashCode();
  }
}
