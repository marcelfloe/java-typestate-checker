package jatyc.key.treeUtils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import jatyc.key.contracts.ContractCreator;
import jatyc.key.contracts.MethodSignature;
import java.io.Writer;
import org.jetbrains.annotations.NotNull;

public class SignatureFinder extends Pretty {
  //TODO: find version mismatch
  //the out-commented code exists due to a version mismatch

  private JCTree.JCMethodDecl methodReference;
  private final JCTree position;
  private JCTree enclClass;
  private JCTree actualEnclClass;

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

  public MethodSignature getMethodSignatur() {
    if (methodReference == null) return null;
    return ContractCreator.createMethodSignature(methodReference, actualEnclClass.type + "");
  }
}
