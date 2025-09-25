package jatyc.key.treePrinter;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import jatyc.JavaTypestateChecker;
import jatyc.key.contracts.ContractCreator;
import jatyc.key.contracts.ContractLog;
import jatyc.key.contracts.MethodInformation;
import jatyc.key.contracts.MethodSignature;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class CommonPrinterFeatures extends Pretty {
  protected Type enclClassType;
  protected final ContractLog contractLog;
  protected final JavaTypestateChecker checker;

  public CommonPrinterFeatures(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog) {
    super(out, sourceOutput);
    this.contractLog = contractLog;
    this.checker = checker;
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
    super.visitImport(tree);
  }

  protected void printTypestateInformationWithoutProtocol(JCTree.JCMethodDecl tree) {
    String contract = getContract(ContractCreator.createMethodSignature(tree, enclClassType + ""), false);
    try {
      print(contract);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  protected void printTypestateInformationWithProtocol(JCTree.JCMethodDecl tree)  {
    String contract = getContract(ContractCreator.createMethodSignature(tree, enclClassType + ""), true);
    try {
      print(contract);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }

  }

  protected String getContract(MethodSignature signature, boolean withProtocolInformation) {
    List<String> requires = new ArrayList<>();
    List<String> ensures = new ArrayList<>();
    List<String> assignable = new ArrayList<>();

    getContract(signature, withProtocolInformation, requires, ensures, assignable);

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
      if (!assignableBuilder.isEmpty()) assignableBuilder.append(" ,");
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
    }

    return contract;
  }

  private void getContract(MethodSignature signature, boolean withProtocolInformation, List<String> requires, List<String> ensures, List<String> assignable) {
    MethodInformation info = contractLog.get(signature); //TODO: child might have parents with contract while not having a contract themselves
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
    for (String parent : info.parentTypes()) { //iterates over all parent types -> no recursion required
      getContractWithoutParents(new MethodSignature(parent, signature.methodName(), signature.parameterTypes()), withProtocolInformation, requires, ensures, assignable);
    }
  }

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

  protected List<String> getValueOnly(JCTree tree) {
    if (tree instanceof JCTree.JCAssign) {
      JCTree rightTree = ((JCTree.JCAssign) tree).rhs;
      if (rightTree instanceof JCTree.JCLiteral) {
        return List.of((((JCTree.JCLiteral) rightTree).value).toString());
      } else if (rightTree instanceof JCTree.JCNewArray) {
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
