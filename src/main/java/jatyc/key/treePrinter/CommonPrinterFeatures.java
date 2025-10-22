package jatyc.key.treePrinter;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import jatyc.JavaTypestateChecker;
import jatyc.key.contracts.ContractCreator;
import jatyc.key.contracts.ContractLog;
import jatyc.key.contracts.MethodInformation;
import jatyc.key.contracts.MethodSignature;
import jatyc.key.treeUtils.SubtypesLog;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

/**
 * This class prints a version of the given tree that does not include any imports and annotations based on JaTyC.
 */
public class CommonPrinterFeatures extends Pretty {
  protected Type enclClassType;
  protected final ContractLog contractLog;
  protected final JavaTypestateChecker checker;
  protected final SubtypesLog subtypes;

  public CommonPrinterFeatures(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog, SubtypesLog subtypes) {
    super(out, sourceOutput);
    this.contractLog = contractLog;
    this.checker = checker;
    this.subtypes = subtypes;
  }

  //@State does not exist, @Ensures is used instead
  @Override
  public void visitAnnotation(JCTree.JCAnnotation tree) {
    switch (tree.annotationType.toString()) {
      case "JML" -> {
        try {
          print("/*@ ");
          print(getValueOnly(tree.args.head).get(0));
          print(" */");
        } catch (IOException e) {
          throw new RuntimeException(e);
        }
      }
      case "Nullable" -> {
        try {
          print("/*@ nullable */");
        } catch (IOException e) {
          throw new RuntimeException(e);
        }
      }
      case "Requires", "Ensures" -> {/* no comments required as the visitMethodDef-method takes care of the typestate information */}
      case "Typestate" -> {/* no comment required as the typestate checker takes care of this */}
      default -> super.visitAnnotation(tree);
    }
  }

  @Override
  public void visitImport(JCTree.JCImport tree) {
    if (tree.toString().matches(".+jatyc\\.lib.+\\r\\n")) { //removes any imports for typestate checker annotations
      return;
    }
    if (tree.toString().matches(".+mungo\\.lib.+\\r\\n")) { //removes any imports for typestate checker annotations (based on mungo)
      return;
    }
    super.visitImport(tree);
  }

  /**
   * Prints the contract information of the given method declaration.
   * This only includes the information based on annotations, but not the information based on protocols.
   * @param tree the method declaration, of which the contract information is printed.
   */
  protected void printTypestateInformationWithoutProtocol(JCTree.JCMethodDecl tree) {
    String contract = getContract(ContractCreator.createMethodSignature(tree, enclClassType + ""), false);
    try {
      print(contract);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }


  /**
   * Prints the contract information of the given method declaration.
   * This includes both the information based on annotations and the information based on protocols.
   * @param tree the method declaration, of which the contract information is printed.
   */
  protected void printTypestateInformationWithProtocol(JCTree.JCMethodDecl tree)  {
    String contract = getContract(ContractCreator.createMethodSignature(tree, enclClassType + ""), true);
    try {
      print(contract);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }

  }

  /**
   * Creates the String of the contract of the given method signature.
   * @param signature the method signature of the method for which the contract is created.
   * @param withProtocolInformation whether the contract has to include the information based on protocols or not.
   * @return a String containing the entire contract of the method. The contract always contains a "public normal_behavior" and a "requires true" to avoid empty contracts.
   */
  protected String getContract(MethodSignature signature, boolean withProtocolInformation) {
    List<String> requires = new ArrayList<>();
    List<String> ensures = new ArrayList<>();
    List<String> assignable = new ArrayList<>();

    getContract(signature, withProtocolInformation, requires, ensures, assignable);
    assignable = assignable.stream().distinct().toList();

    StringBuilder requiresBuilder = new StringBuilder();
    StringBuilder ensuresBuilder = new StringBuilder();
    StringBuilder assignableBuilder = new StringBuilder();

    for (String s : requires) {
      if (s.isBlank()) continue;
      if (!requiresBuilder.isEmpty()) requiresBuilder.append(" || ");
      requiresBuilder.append(s);
    }
    for (String s : ensures) {
      if (s.isBlank()) continue;
      if (!ensuresBuilder.isEmpty()) ensuresBuilder.append(" && ");
      ensuresBuilder.append(s);
    }
    for (String s : assignable) {
      if (s.isBlank()) continue;
      if (!assignableBuilder.isEmpty()) assignableBuilder.append(", ");
      assignableBuilder.append(s);
    }

    String contract = "";
    if (!requiresBuilder.isEmpty()) {
      contract += "\n//@ requires " + requiresBuilder + ";";
    }
    if (!ensuresBuilder.isEmpty()) {
      contract += "\n//@ ensures " + ensuresBuilder + ";";
    }
    if (!assignableBuilder.isEmpty()) {
      contract += "\n//@ assignable " + assignableBuilder + ";";
    } else if (withProtocolInformation) {
      contract += "\n//@ assignable \\nothing" + assignableBuilder + ";";
    }


    return "\n//@ public normal_behavior \n//@ requires true;" + contract;
  }


  /**
   * Gets all statements of the contract of the given method signature and stores them in the given lists.
   * This contract does also contain parent and child information.
   * @param signature the method signature of the method for which the contract is created.
   * @param withProtocolInformation whether the contract has to include the information based on protocols or not.
   * @param requires the list of all requires statements.
   * @param ensures the list of all ensures statements.
   * @param assignable the list of all assignable statements.
   */
  private void getContract(MethodSignature signature, boolean withProtocolInformation, List<String> requires, List<String> ensures, List<String> assignable) {
    MethodInformation info = contractLog.get(signature); //TODO: child might have parents with contract while not having a contract themselves (is this already handled by JaTyC?)
    if (info == null) return; //method hasn't been logged
    if (withProtocolInformation) {
      requires.add(info.getRequiresWithProtocol());
      ensures.add(info.getEnsuresWithProtocol());
      assignable.add(info.getAssignableWithProtocol());
      //If the assignable clause doesn't include the class state, then the method isn't part of the protocol and therefore it is an anytime method.
      //Anytime methods are not allowed to change any state information of the object they are called on.
      if (info.getAssignableWithProtocol().contains(info.signature().classType() + "State")) {
        //assignable clauses need to hold references to their subtypes to avoid conflicting contracts
        assignable.addAll(subtypes.get(info.signature().classType()).stream().map(t -> t + "State").toList());
      }
    } else {
      requires.add(info.getRequiresWithoutProtocol());
      ensures.add(info.getEnsuresWithoutProtocol());
      assignable.add(info.getAssignableWithoutProtocol());
    }
    //assignable clauses need to hold references to their subtypes to avoid conflicting contracts
    for (int i = 0; i < info.parameterNames().size(); i++) {
      String paramName = info.parameterNames().get(i);
      for (String type : subtypes.get(info.signature().parameterTypes().get(i))) {
        assignable.add(paramName + "." + type + "State");
      }
    }
    //including the parent contracts
    for (String parent : info.parentTypes()) { //iterates over all parent types (no recursion required as record already contains all parent types)
      getContractWithoutParents(new MethodSignature(parent, signature.methodName(), signature.parameterTypes()), withProtocolInformation, requires, ensures, assignable);
    }
  }

  /**
   * Gets all statements of the contract of the given method signature and stores them in the given lists.
   * This contract does only contain the information for the type in the signature and neither parent nor child information.
   * @param signature the method signature of the method for which the contract is created.
   * @param withProtocolInformation whether the contract has to include the information based on protocols or not.
   * @param requires the list of all requires statements.
   * @param ensures the list of all ensures statements.
   * @param assignable the list of all assignable statements.
   */
  private void getContractWithoutParents(MethodSignature signature, boolean withProtocolInformation, List<String> requires, List<String> ensures, List<String> assignable) {
    MethodInformation info = contractLog.get(signature);
    if (info == null) return;
    if (withProtocolInformation) {
      requires.add(info.getRequiresWithProtocol());
      ensures.add(info.getEnsuresWithProtocol());
      assignable.add(info.getAssignableWithProtocol());
    } else {
      requires.add(info.getRequiresWithoutProtocol());
      ensures.add(info.getEnsuresWithoutProtocol());
      assignable.add(info.getAssignableWithoutProtocol());
    }
  }

  /**
   * Returns the content of the right hand side of the assign.
   * @param tree the JCTree, which contains the required value.
   * @return if tree is a JCAssign then it returns the right hand side of that assign, otherwise null
   */
  protected List<String> getValueOnly(JCTree tree) {
    if (tree instanceof JCTree.JCAssign) {
      JCTree rightTree = ((JCTree.JCAssign) tree).rhs;
      if (rightTree instanceof JCTree.JCLiteral) { //only one element
        return List.of((((JCTree.JCLiteral) rightTree).value).toString());
      } else if (rightTree instanceof JCTree.JCNewArray) { //multiple elements
        List<String> value = new ArrayList<>();
        for (JCTree.JCExpression elem : ((JCTree.JCNewArray) rightTree).elems) {
          if (elem  instanceof JCTree.JCLiteral) {
            value.add(((JCTree.JCLiteral) elem).value.toString());
          }
        }
        return value;
      }
    }
    return null;
  }

}
