package jatyc.key;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.util.Name;
import jatyc.JavaTypestateChecker;
import jatyc.typestate.graph.DecisionState;
import jatyc.typestate.graph.Graph;
import jatyc.typestate.graph.State;
import jatyc.util.multimap.BiMap;
import jatyc.util.multimap.QuadMap;
import jatyc.utils.ClassUtils;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class TreePrinterForProofs extends TreePrinterWithoutBodies {
  private JavaTypestateChecker checker;
  private Type enclClassType;
  private String ghostVar;
  private TreePrinterWithoutProtocol methodPrinter;

  public TreePrinterForProofs(Writer out, boolean sourceOutput, JavaTypestateChecker checker) {
    super(out, sourceOutput, checker);
    this.checker = checker;
    this.methodPrinter = new TreePrinterWithoutProtocol(out, sourceOutput, checker);
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
