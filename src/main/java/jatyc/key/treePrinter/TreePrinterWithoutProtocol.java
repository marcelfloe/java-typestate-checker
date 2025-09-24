package jatyc.key.treePrinter;

import com.sun.tools.javac.tree.JCTree;
import jatyc.key.contracts.ContractLog;
import java.io.Writer;

/**
 * This class prints a version of the given tree that does not include any protocol information of this-pointers,
 * but all typestate information based on annotations.
 */
//TODO: also print given assertions (place assertions for entire method starting at the position with the assumed mistake, as checker doesn't check after that)
//TODO: are assumptions required? -> if yes the ensures-statements need modification as \old can't be used => ghostvars required
//TODO: assertion and assumption not required as covered by contracts (ensures/requires)
//TODO: requires assertion at method end for protocol completion; actually at every block-end/return
// Block-End -> new local variables
// Return -> all local variables
// return statement might require temp variable
public class TreePrinterWithoutProtocol extends CommonPrinterFeatures {

  public TreePrinterWithoutProtocol(Writer out, boolean sourceOutput, ContractLog contractLog) {
    super(out, sourceOutput, contractLog);
  }

  //annotations and imports are managed by super class

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    printTypestateInformationWithoutProtocol(tree);
    super.visitMethodDef(tree);
  }

  @Override
  public void visitBlock(JCTree.JCBlock tree) {
    super.visitBlock(tree);
    //TODO: insert assertion at end of block checking protocol completion (end/droppable) for all local variables inside the block
  }

  @Override
  public void visitReturn(JCTree.JCReturn tree) {
    super.visitReturn(tree);
    //TODO: insert assertion at return checking protocol completion (end/droppable) for all local variables inside the method
    // this will require temporary variables in case of called methods, e.g. "return foo()"
  }
}
