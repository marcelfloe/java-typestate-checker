package jatyc.key.treePrinter;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import jatyc.JavaTypestateChecker;
import jatyc.core.JavaType;
import jatyc.key.contracts.ContractLog;
import jatyc.key.treeUtils.SubtypesLog;

import java.io.IOException;
import java.io.Writer;

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class TreePrinterWithoutBodies extends CommonPrinterFeatures {
  private boolean printGhostVar = false;
  private boolean insideMethod = false;

  public TreePrinterWithoutBodies(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog, SubtypesLog subtypes) {
    super(out, sourceOutput, checker, contractLog, subtypes);
  }

  //annotations and imports are managed by super class

  @Override
  public void visitClassDef(JCTree.JCClassDecl tree) { //initializing the ghost variable if a protocol exists
    boolean temp = insideMethod;
    insideMethod = false;

    Type prevClassType = enclClassType;
    enclClassType = tree.type;

    boolean ghostVarTemp = printGhostVar;
    printGhostVar = tree.type != null && checker.getUtils().classUtils.hasProtocol(tree.type) && checker.getUtils().typeIntroducer.getJavaType(tree.type).getSuperTypes().stream().filter(JavaType::hasProtocol).toList().isEmpty();

    super.visitClassDef(tree);

    enclClassType = prevClassType;
    printGhostVar = ghostVarTemp;
    insideMethod = temp;
  }

  @Override
  public void printBlock(com.sun.tools.javac.util.List<? extends JCTree> stats) throws IOException {
    if (insideMethod || !printGhostVar) {
      super.printBlock(stats);
      return;
    }
    printBlockWithGhostVar(stats);

  }

  public void printBlockWithGhostVar(com.sun.tools.javac.util.List<? extends JCTree> stats) throws IOException { //copy from Pretty, but with inserted assertion
    print("{");
    println();
    for (String type : subtypes.get(enclClassType.baseType().toString())) {
      print("//@ public ghost instance int " + type + "State = -1;\n");
    }
    printStats(stats);
    print("}");
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    boolean temp = insideMethod;
    insideMethod = true;
    printTypestateInformationWithProtocol(tree); //prints typestate information based on protocol of "this"-class

    JCTree.JCMethodDecl treeClone = (JCTree.JCMethodDecl) tree.clone();
    treeClone.body = null; //KeY uses method stubs without body

    super.visitMethodDef(treeClone);
    insideMethod = temp;
  }

}
