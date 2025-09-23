package jatyc.key.treePrinter;

import com.sun.tools.javac.tree.JCTree;
import jatyc.JavaTypestateChecker;
import jatyc.key.contracts.ContractCreator;
import jatyc.key.contracts.ContractLog;
import jatyc.key.contracts.MethodSignature;
import java.io.Writer;

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class TreePrinterForProofs extends TreePrinterWithoutBodies {
  private final TreePrinterWithoutProtocol methodPrinter;

  private final MethodSignature methodSignature;

  public TreePrinterForProofs(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog, MethodSignature methodSignature) {
    super(out, sourceOutput, checker, contractLog);
    this.methodPrinter = new TreePrinterWithoutProtocol(out, sourceOutput, contractLog);
    this.methodSignature = methodSignature;
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    if (methodNeedsReplacement(tree)) {
      tree.accept(methodPrinter);
    } else {
      super.visitMethodDef(tree);
    }
  }

  private boolean methodNeedsReplacement(JCTree.JCMethodDecl tree) {
    return ContractCreator.createMethodSignature(tree, enclClassType + "").equals(methodSignature);
  }
}
