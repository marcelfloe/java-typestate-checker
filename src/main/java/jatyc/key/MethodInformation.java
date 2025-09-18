package jatyc.key;

import java.util.List;

public record MethodInformation(MethodSignature signature, ContractInformation annotationInformation, ContractInformation protocolInformation, List<String> parentTypes) {

  public String getRequiresWithoutProtocol() {
    return annotationInformation().getRequires();
  }

  public String getRequiresWithProtocol() {
    if (annotationInformation().getRequires().isBlank()) return protocolInformation.getRequires();
    if (protocolInformation.getRequires().isBlank()) return annotationInformation.getRequires();
    return annotationInformation().getRequires() + " && " + protocolInformation.getRequires();

  }

  public String getEnsuresWithoutProtocol() {
    return annotationInformation.getEnsures();
  }

  public String getEnsuresWithProtocol() {
    if (annotationInformation().getEnsures().isBlank()) return protocolInformation.getEnsures();
    if (protocolInformation.getEnsures().isBlank()) return annotationInformation.getEnsures();
    return annotationInformation().getEnsures() + " && " + protocolInformation.getEnsures();
  }

  public String getAssignableWithoutProtocol() {
    return annotationInformation().getAssignable();
  }

  public String getAssignableWithProtocol() {
    if (annotationInformation().getAssignable().isBlank()) return protocolInformation.getAssignable();
    if (protocolInformation.getAssignable().isBlank()) return annotationInformation.getAssignable();
    return annotationInformation().getAssignable() + " ," + protocolInformation.getAssignable();
  }
}
