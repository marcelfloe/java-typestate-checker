package jatyc.key;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import jatyc.JavaTypestateChecker;
import java.io.IOException;
import java.io.Writer;

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class TreePrinterWithoutBodies extends CommonPrinterFeatures {
  private JavaTypestateChecker checker;
  private String ghostVar;

  public TreePrinterWithoutBodies(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog) {
    super(out, sourceOutput, contractLog);
    this.checker = checker;
  }

  //annotations and imports are managed by super class

  @Override
  public void visitClassDef(JCTree.JCClassDecl tree) {
    Type prevClassType = enclClassType;
    enclClassType = tree.type;
    String prevGhostVar = ghostVar;
    ghostVar = tree.getSimpleName().toString() + "State";
    if (tree.type != null && checker.getUtils().classUtils.hasProtocol(tree.type)) {
      try {
        print("//@ public ghost int " + ghostVar + " = -1;\n");
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }
    super.visitClassDef(tree);
    enclClassType = prevClassType;
    ghostVar = prevGhostVar;
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    printTypestateInformationWithProtocol(tree); //prints typestate information based on protocol of "this"-class

    JCTree.JCMethodDecl treeClone = (JCTree.JCMethodDecl) tree.clone();
    treeClone.body = null; //KeY uses method stubs without body

    super.visitMethodDef(treeClone);
  }

}
