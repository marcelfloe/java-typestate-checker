package jatyc.key.treeUtils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import jatyc.key.contracts.ContractCreator;
import jatyc.key.contracts.MethodSignature;
import java.io.Writer;
import org.jetbrains.annotations.NotNull;

/**
 * This class identifies the method signature of the method which contains the given position.
 */
public class SignatureFinder extends Pretty {
  private JCTree.JCMethodDecl methodReference;
  private final JCTree position;
  private JCTree enclClass;
  private JCTree actualEnclClass; //stores the class enclosing the position in case of multiple (sub-)classes

  public SignatureFinder(JCTree position) {
    super(new Writer() {
      @Override
      public void write(@NotNull char[] cbuf, int off, int len) {
      }

      @Override
      public void flush() {
      }

      @Override
      public void close() {
      }
    }, true); //Pretty is not actually supposed to print anything, but to manage calling the correct visit functions
    this.position = position;
  }

  @Override
  public void visitClassDef(JCTree.JCClassDecl tree) {
    JCTree temp = enclClass;
    enclClass = tree;
    super.visitClassDef(tree);
    enclClass = temp;
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    if (tree.pos <= position.pos) {
      methodReference = tree;
      actualEnclClass = enclClass;
    }
    super.visitMethodDef(tree);
  }

  public MethodSignature getMethodSignature() {
    if (methodReference == null) return null;
    return ContractCreator.createMethodSignature(methodReference, actualEnclClass.type + "");
  }
}
