package jatyc.key;

import com.sun.tools.javac.tree.JCTree;
import jatyc.JavaTypestateChecker;
import java.io.Writer;

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class TreePrinterForProofs extends TreePrinterWithoutBodies {
  private TreePrinterWithoutProtocol methodPrinter;

  public TreePrinterForProofs(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog) {
    super(out, sourceOutput, checker, contractLog);
    this.methodPrinter = new TreePrinterWithoutProtocol(out, sourceOutput, checker, contractLog);
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
    return true;
  }
}
