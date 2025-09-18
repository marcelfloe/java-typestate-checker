package jatyc.key;

import com.sun.tools.javac.tree.JCTree;
import jatyc.JavaTypestateChecker;
import java.io.Writer;

/**
 * This class prints a version of the given tree that does not include any protocol information of this-pointers,
 * but all typestate information based on annotations.
 */
//TODO: also print given assertions (place assertions for entire method starting at the position with the assumed mistake, as checker doesn't check after that)
public class TreePrinterWithoutProtocol extends CommonPrinterFeatures {

  public TreePrinterWithoutProtocol(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog) {
    super(out, sourceOutput, contractLog);
  }

  //annotations and imports are managed by super class

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    printTypestateInformationWithoutProtocol(tree);
    super.visitMethodDef(tree);
  }
}
