package jatyc.key.treeUtils;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import jatyc.JavaTypestateChecker;
import jatyc.core.JavaType;
import org.jetbrains.annotations.NotNull;

import java.io.Writer;
import java.util.HashSet;
import java.util.Stack;

public class SubtypesLogger extends Pretty {
  //TODO: find version mismatch
  //the out-commented code exists due to a version mismatch

  private final SubtypesLog subtypes;
  private final JavaTypestateChecker checker;

  public SubtypesLogger(SubtypesLog subtypes, JavaTypestateChecker checker) {
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
    this.subtypes = subtypes;
    this.checker = checker;
  }

  @Override
  public void visitClassDef(JCTree.JCClassDecl tree) {
    logSubtype(tree.type);
    super.visitClassDef(tree);
  }

  private void logSubtype(Type type) {
    logSubtypes(checker.getUtils().typeIntroducer.getJavaType(type), new Stack<>());
  }

  private void logSubtypes(JavaType type, Stack<JavaType> subTypes) {
    if (type.hasProtocol()) subTypes.push(type);
    for (JavaType superType : type.getSuperTypes()) {
      logSubtypes(superType, subTypes);
    }
    String key = type.getOriginal().baseType().toString();
    this.subtypes.get(key).addAll(subTypes.stream().map(t -> t.getOriginal().baseType().toString()).toList());
    if (type.hasProtocol()) subTypes.pop();
  }
}
