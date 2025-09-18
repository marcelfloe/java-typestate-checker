package jatyc.key;

import java.util.List;

public record ContractInformation(List<String> requiresStatements, List<String> ensuresStatements, List<String> assignableStatements) {

  public String getRequires() {
    StringBuilder requires = new StringBuilder();
    if (requiresStatements.isEmpty()) return requires.toString();
    requires.append(requiresStatements.get(0));
    for (int i = 1; i < requiresStatements.size(); i++) {
      requires.append(" && ").append(requiresStatements.get(i));
    }
    return requires.toString();
  }

  public String getEnsures() {
    StringBuilder ensures = new StringBuilder();
    if (ensuresStatements.isEmpty()) return ensures.toString();
    ensures.append(ensuresStatements.get(0));
    for (int i = 1; i < ensuresStatements.size(); i++) {
      ensures.append(" && ").append(ensuresStatements.get(i));
    }
    return ensures.toString();
  }

  public String getAssignable() {
    StringBuilder assignable = new StringBuilder();
    if (assignableStatements.isEmpty()) return assignable.toString();
    assignable.append(assignableStatements.get(0));
    for (int i = 1; i < assignableStatements.size(); i++) {
      assignable.append(", ").append(assignableStatements.get(i));
    }
    return assignable.toString();
  }
}
