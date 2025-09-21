package jatyc.key.treePrinter;

import com.sun.tools.javac.tree.JCTree;
import jatyc.JavaTypestateChecker;
import jatyc.key.contracts.ContractLog;
import java.io.Writer;

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class TreePrinterForProofs extends TreePrinterWithoutBodies {
  private final TreePrinterWithoutProtocol methodPrinter;

  private final JCTree errorSource;
  private final String messageKeY;
  private final Object[] args;

  public TreePrinterForProofs(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog, JCTree errorSource, String messageKey, Object... args) {
    super(out, sourceOutput, checker, contractLog);
    this.methodPrinter = new TreePrinterWithoutProtocol(out, sourceOutput, contractLog, errorSource, messageKey, args);
    this.errorSource = errorSource;
    this.messageKeY = messageKey;
    this.args = args;
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    if (methodNeedsReplacement(tree)) {
      tree.accept(methodPrinter);
    } else {
      super.visitMethodDef(tree);
    }
  }

  //TODO: identify which method needs replacement
  private boolean methodNeedsReplacement(JCTree.JCMethodDecl tree) {
    return false;
  }
}
