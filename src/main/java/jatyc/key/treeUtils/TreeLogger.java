package jatyc.key.treeUtils;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import java.io.Writer;
import java.util.HashMap;
import org.jetbrains.annotations.NotNull;

/**
 * This class logs for every JCTree, to which file it belongs.
 */
public class TreeLogger extends Pretty {
  //TODO: find version mismatch
  //the out-commented code exists due to a version mismatch
  private final HashMap<JCTree, String> jcTrees;
  private final String fileReference;

  public TreeLogger(HashMap<JCTree, String> jcTrees, String fileReference) {
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
    this.jcTrees = jcTrees;
    this.fileReference = fileReference;
  }

  @Override
  public void visitTopLevel(JCTree.JCCompilationUnit that)    {
    jcTrees.put(that, fileReference);
    super.visitTopLevel(that);
  }
  @Override
  public void visitPackageDef(JCTree.JCPackageDecl that)      {
    jcTrees.put(that, fileReference);
    super.visitPackageDef(that);
  }
  @Override
  public void visitImport(JCTree.JCImport that)               {
    jcTrees.put(that, fileReference);
    super.visitImport(that);
  }
  @Override
  public void visitClassDef(JCTree.JCClassDecl that)          {
    jcTrees.put(that, fileReference);
    super.visitClassDef(that);
  }
  @Override
  public void visitMethodDef(JCTree.JCMethodDecl that)        {
    jcTrees.put(that, fileReference);
    super.visitMethodDef(that);
  }
  @Override
  public void visitVarDef(JCTree.JCVariableDecl that)         {
    jcTrees.put(that, fileReference);
    super.visitVarDef(that);
  }
  @Override
  public void visitSkip(JCTree.JCSkip that)                   {
    jcTrees.put(that, fileReference);
    super.visitSkip(that);
  }
  @Override
  public void visitBlock(JCTree.JCBlock that)                 {
    jcTrees.put(that, fileReference);
    super.visitBlock(that);
  }
  @Override
  public void visitDoLoop(JCTree.JCDoWhileLoop that)          {
    jcTrees.put(that, fileReference);
    super.visitDoLoop(that);
  }
  @Override
  public void visitWhileLoop(JCTree.JCWhileLoop that)         {
    jcTrees.put(that, fileReference);
    super.visitWhileLoop(that);
  }
  @Override
  public void visitForLoop(JCTree.JCForLoop that)             {
    jcTrees.put(that, fileReference);
    super.visitForLoop(that);
  }
  @Override
  public void visitForeachLoop(JCTree.JCEnhancedForLoop that) {
    jcTrees.put(that, fileReference);
    super.visitForeachLoop(that);
  }
  @Override
  public void visitLabelled(JCTree.JCLabeledStatement that)   {
    jcTrees.put(that, fileReference);
    super.visitLabelled(that);
  }
  @Override
  public void visitSwitch(JCTree.JCSwitch that)               {
    jcTrees.put(that, fileReference);
    super.visitSwitch(that);
  }
  @Override
  public void visitCase(JCTree.JCCase that)                   {
    jcTrees.put(that, fileReference);
    super.visitCase(that);
  }
  /*@Override
  public void visitSwitchExpression(JCTree.JCSwitchExpression that)               {
    jcTrees.put(that, fileReference);
    super.visitSwitchExpression(that);
  }*/
  @Override
  public void visitSynchronized(JCTree.JCSynchronized that)   {
    jcTrees.put(that, fileReference);
    super.visitSynchronized(that);
  }
  @Override
  public void visitTry(JCTree.JCTry that)                     {
    jcTrees.put(that, fileReference);
    super.visitTry(that);
  }
  @Override
  public void visitCatch(JCTree.JCCatch that)                 {
    jcTrees.put(that, fileReference);
    super.visitCatch(that);
  }
  @Override
  public void visitConditional(JCTree.JCConditional that)     {
    jcTrees.put(that, fileReference);
    super.visitConditional(that);
  }
  @Override
  public void visitIf(JCTree.JCIf that)                       {
    jcTrees.put(that, fileReference);
    super.visitIf(that);
  }
  @Override
  public void visitExec(JCTree.JCExpressionStatement that)    {
    jcTrees.put(that, fileReference);
    super.visitExec(that);
  }
  @Override
  public void visitBreak(JCTree.JCBreak that)                 {
    jcTrees.put(that, fileReference);
    super.visitBreak(that);
  }
  /*@Override
  public void visitYield(JCTree.JCYield that)                 {
    jcTrees.put(that, fileReference);
    super.visitYield(that);
  }*/
  @Override
  public void visitContinue(JCTree.JCContinue that)           {
    jcTrees.put(that, fileReference);
    super.visitContinue(that);
  }
  @Override
  public void visitReturn(JCTree.JCReturn that)               {
    jcTrees.put(that, fileReference);
    super.visitReturn(that);
  }
  @Override
  public void visitThrow(JCTree.JCThrow that)                 {
    jcTrees.put(that, fileReference);
    super.visitThrow(that);
  }
  @Override
  public void visitAssert(JCTree.JCAssert that)               {
    jcTrees.put(that, fileReference);
    super.visitAssert(that);
  }
  @Override
  public void visitApply(JCTree.JCMethodInvocation that)      {
    jcTrees.put(that, fileReference);
    super.visitApply(that);
  }
  @Override
  public void visitNewClass(JCTree.JCNewClass that)           {
    jcTrees.put(that, fileReference);
    super.visitNewClass(that);
  }
  @Override
  public void visitNewArray(JCTree.JCNewArray that)           {
    jcTrees.put(that, fileReference);
    super.visitNewArray(that);
  }
  @Override
  public void visitLambda(JCTree.JCLambda that)               {
    jcTrees.put(that, fileReference);
    super.visitLambda(that);
  }
  @Override
  public void visitParens(JCTree.JCParens that)               {
    jcTrees.put(that, fileReference);
    super.visitParens(that);
  }
  @Override
  public void visitAssign(JCTree.JCAssign that)               {
    jcTrees.put(that, fileReference);
    super.visitAssign(that);
  }
  @Override
  public void visitAssignop(JCTree.JCAssignOp that)           {
    jcTrees.put(that, fileReference);
    super.visitAssignop(that);
  }
  @Override
  public void visitUnary(JCTree.JCUnary that)                 {
    jcTrees.put(that, fileReference);
    super.visitUnary(that);
  }
  @Override
  public void visitBinary(JCTree.JCBinary that)               {
    jcTrees.put(that, fileReference);
    super.visitBinary(that);

  }
  @Override
  public void visitTypeCast(JCTree.JCTypeCast that)           {
    jcTrees.put(that, fileReference);
    super.visitTypeCast(that);
  }
  @Override
  public void visitTypeTest(JCTree.JCInstanceOf that)         {
    jcTrees.put(that, fileReference);
    super.visitTypeTest(that);
  }
  /*@Override
  public void visitBindingPattern(JCTree.JCBindingPattern that) {
    jcTrees.put(that, fileReference);
    super.visitBindingPattern(that);
  }*/
  /*@Override
  public void visitDefaultCaseLabel(JCTree.JCDefaultCaseLabel that) {
    jcTrees.put(that, fileReference);
    super.visitDefaultCaseLabel(that);
  }*/
  /*@Override
  public void visitParenthesizedPattern(JCTree.JCParenthesizedPattern that) {
    jcTrees.put(that, fileReference);
    super.visitParenthesizedPattern(that);
  }*/
  /*@Override
  public void visitGuardPattern(JCTree.JCGuardPattern that) {
    jcTrees.put(that, fileReference);
    super.visitGuardPattern(that);
  }*/
  @Override
  public void visitIndexed(JCTree.JCArrayAccess that)         {
    jcTrees.put(that, fileReference);
    super.visitIndexed(that);
  }
  @Override
  public void visitSelect(JCTree.JCFieldAccess that)          {
    jcTrees.put(that, fileReference);
    super.visitSelect(that);
  }
  @Override
  public void visitReference(JCTree.JCMemberReference that)   {
    jcTrees.put(that, fileReference);
    super.visitReference(that);
  }
  @Override
  public void visitIdent(JCTree.JCIdent that)                 {
    jcTrees.put(that, fileReference);
    super.visitIdent(that);
  }
  @Override
  public void visitLiteral(JCTree.JCLiteral that)             {
    jcTrees.put(that, fileReference);
    super.visitLiteral(that);
  }
  @Override
  public void visitTypeIdent(JCTree.JCPrimitiveTypeTree that) {
    jcTrees.put(that, fileReference);
    super.visitTypeIdent(that);
  }
  @Override
  public void visitTypeArray(JCTree.JCArrayTypeTree that)     {
    jcTrees.put(that, fileReference);
    super.visitTypeArray(that);
  }
  @Override
  public void visitTypeApply(JCTree.JCTypeApply that)         {
    jcTrees.put(that, fileReference);
    super.visitTypeApply(that);
  }
  @Override
  public void visitTypeUnion(JCTree.JCTypeUnion that)         {
    jcTrees.put(that, fileReference);
    super.visitTypeUnion(that);
  }
  @Override
  public void visitTypeIntersection(JCTree.JCTypeIntersection that)  {
    jcTrees.put(that, fileReference);
    super.visitTypeIntersection(that);
  }
  @Override
  public void visitTypeParameter(JCTree.JCTypeParameter that) {
    jcTrees.put(that, fileReference);
    super.visitTypeParameter(that);
  }
  @Override
  public void visitWildcard(JCTree.JCWildcard that)           {
    jcTrees.put(that, fileReference);
    super.visitWildcard(that);
  }
  @Override
  public void visitTypeBoundKind(JCTree.TypeBoundKind that)   {
    jcTrees.put(that, fileReference);
    super.visitTypeBoundKind(that);
  }
  @Override
  public void visitAnnotation(JCTree.JCAnnotation that)       {
    jcTrees.put(that, fileReference);
    super.visitAnnotation(that);
  }
  @Override
  public void visitModifiers(JCTree.JCModifiers that)         {
    jcTrees.put(that, fileReference);
    super.visitModifiers(that);
  }
  @Override
  public void visitAnnotatedType(JCTree.JCAnnotatedType that) {
    jcTrees.put(that, fileReference);
    super.visitAnnotatedType(that);
  }
  @Override
  public void visitErroneous(JCTree.JCErroneous that)         {
    jcTrees.put(that, fileReference);
    super.visitErroneous(that);
  }
  @Override
  public void visitModuleDef(JCTree.JCModuleDecl that)        {
    jcTrees.put(that, fileReference);
    super.visitModuleDef(that);
  }
  @Override
  public void visitExports(JCTree.JCExports that)             {
    jcTrees.put(that, fileReference);
    super.visitExports(that);
  }
  @Override
  public void visitOpens(JCTree.JCOpens that)                 {
    jcTrees.put(that, fileReference);
    super.visitOpens(that);
  }
  @Override
  public void visitProvides(JCTree.JCProvides that)           {
    jcTrees.put(that, fileReference);
    super.visitProvides(that);
  }
  @Override
  public void visitRequires(JCTree.JCRequires that)           {
    jcTrees.put(that, fileReference);
    super.visitRequires(that);
  }
  @Override
  public void visitUses(JCTree.JCUses that)                   {
    jcTrees.put(that, fileReference);
    super.visitUses(that);
  }
  @Override
  public void visitLetExpr(JCTree.LetExpr that)               {
    jcTrees.put(that, fileReference);
    super.visitLetExpr(that);
  }
}
