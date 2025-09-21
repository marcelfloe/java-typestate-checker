package jatyc.key.treePrinter;

import com.sun.tools.javac.tree.JCTree;
import jatyc.key.contracts.ContractLog;
import java.io.Writer;

/**
 * This class prints a version of the given tree that does not include any protocol information of this-pointers,
 * but all typestate information based on annotations.
 */
//TODO: also print given assertions (place assertions for entire method starting at the position with the assumed mistake, as checker doesn't check after that)
public class TreePrinterWithoutProtocol extends CommonPrinterFeatures {
  private final JCTree errorSource;
  private final String messageKeY;
  private final Object[] args;

  public TreePrinterWithoutProtocol(Writer out, boolean sourceOutput, ContractLog contractLog, JCTree errorSource, String messageKey, Object... args) {
    super(out, sourceOutput, contractLog);
    this.errorSource = errorSource;
    this.messageKeY = messageKey;
    this.args = args;
  }

  //annotations and imports are managed by super class

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    printTypestateInformationWithoutProtocol(tree);
    super.visitMethodDef(tree);
  }
}
