package jatyc.key;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import jatyc.JavaTypestateChecker;
import jatyc.typestate.graph.State;
import jatyc.utils.ClassUtils;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

/**
 * This class prints a version of the given tree that does not include any protocol information of this-pointers,
 * but all typestate information based on annotations.
 */
//TODO: also print given assertions
public class TreePrinterWithoutProtocol extends CommonPrinterFeatures {
  private JavaTypestateChecker checker;

  public TreePrinterWithoutProtocol(Writer out, boolean sourceOutput, JavaTypestateChecker checker) {
    super(out, sourceOutput);
    this.checker = checker;
  }

  //annotations and imports are managed by super class

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    ClassUtils utils = checker.getUtils().classUtils;

    printTypestateAnnotationInformation(tree, utils);

    super.visitMethodDef(tree);
  }
}
