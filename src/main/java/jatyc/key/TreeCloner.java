package jatyc.key;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import java.io.IOException;
import java.io.Writer;
import org.jetbrains.annotations.NotNull;

public class TreeCloner extends Pretty {
  //TODO: find version mismatch
  //the out-commented code exists due to a version mismatch

  public TreeCloner() {
    super(new Writer() {
      @Override
      public void write(@NotNull char[] cbuf, int off, int len) throws IOException {
      }

      @Override
      public void flush() throws IOException {
      }

      @Override
      public void close() throws IOException {
      }
    }, true); //Pretty is not actually supposed to print anything, but to manage calling the correct visit functions
  }

  @Override
  public void visitTopLevel(JCTree.JCCompilationUnit that)    {
    that.defs = that.defs == null ? null : that.defs.map(t -> (JCTree) t.clone());
    super.visitTopLevel(that);
  }
  @Override
  public void visitPackageDef(JCTree.JCPackageDecl that)      {
    that.annotations = that.annotations == null ? null : that.annotations.map(t -> (JCTree.JCAnnotation) t.clone());
    that.pid = that.pid == null ? null : (JCTree.JCExpression) that.pid.clone();
    super.visitPackageDef(that);
  }
  @Override
  public void visitImport(JCTree.JCImport that)               {
    that.qualid = that.qualid == null ? null : (JCTree) that.qualid.clone();
    super.visitImport(that);
  }
  @Override
  public void visitClassDef(JCTree.JCClassDecl that)          {
    that.defs = that.defs == null ? null : that.defs.map(t -> (JCTree) t.clone());
    that.extending = that.extending == null ? null : (JCTree.JCExpression) that.extending.clone();
    that.implementing = that.implementing == null ? null : that.implementing.map(t -> (JCTree.JCExpression) t.clone());
    //that.permitting = that.permitting == null ? null : that.permitting.map(t -> (JCTree.JCExpression) t.clone());
    that.mods = that.mods == null ? null : (JCTree.JCModifiers) that.mods.clone();
    that.typarams = that.typarams == null ? null : that.typarams.map(t -> (JCTree.JCTypeParameter) t.clone());
    super.visitClassDef(that);
  }
  @Override
  public void visitMethodDef(JCTree.JCMethodDecl that)        {
    that.mods = that.mods == null ? null : (JCTree.JCModifiers) that.mods.clone();
    that.restype = that.restype == null ? null : (JCTree.JCExpression) that.restype.clone();
    that.defaultValue = that.defaultValue == null ? null : (JCTree.JCExpression) that.defaultValue.clone();
    that.body = that.body == null ? null : (JCTree.JCBlock) that.body.clone();
    that.recvparam = that.recvparam == null ? null : (JCTree.JCVariableDecl) that.recvparam.clone();
    that.params = that.params == null ? null : that.params.map(t -> (JCTree.JCVariableDecl) t.clone());
    that.thrown = that.thrown == null ? null : that.thrown.map(t -> (JCTree.JCExpression) t.clone());
    that.typarams = that.typarams == null ? null : that.typarams.map(t -> (JCTree.JCTypeParameter) t.clone());
    super.visitMethodDef(that);
  }
  @Override
  public void visitVarDef(JCTree.JCVariableDecl that)         {
    that.mods = that.mods == null ? null : (JCTree.JCModifiers) that.mods.clone();
    that.vartype = that.vartype == null ? null : (JCTree.JCExpression) that.vartype.clone();
    that.init = that.init == null ? null : (JCTree.JCExpression) that.init.clone();
    that.nameexpr = that.nameexpr == null ? null : (JCTree.JCExpression) that.nameexpr.clone();
    super.visitVarDef(that);
  }
  @Override
  public void visitSkip(JCTree.JCSkip that)                   {
    super.visitSkip(that);
  }
  @Override
  public void visitBlock(JCTree.JCBlock that)                 {
    that.stats = that.stats == null ? null : that.stats.map(t -> (JCTree.JCStatement) t.clone());
    super.visitBlock(that);
  }
  @Override
  public void visitDoLoop(JCTree.JCDoWhileLoop that)          {
    that.body = that.body == null ? null : (JCTree.JCStatement) that.body.clone();
    that.cond = that.cond == null ? null : (JCTree.JCExpression) that.cond.clone();
    super.visitDoLoop(that);
  }
  @Override
  public void visitWhileLoop(JCTree.JCWhileLoop that)         {
    that.body = that.body == null ? null : (JCTree.JCStatement) that.body.clone();
    that.cond = that.cond == null ? null : (JCTree.JCExpression) that.cond.clone();
    super.visitWhileLoop(that);
  }
  @Override
  public void visitForLoop(JCTree.JCForLoop that)             {
    that.body = that.body == null ? null : (JCTree.JCStatement) that.body.clone();
    that.cond = that.cond == null ? null : (JCTree.JCExpression) that.cond.clone();
    that.init = that.init == null ? null : that.init.map(t -> (JCTree.JCStatement) t.clone());
    that.step = that.step == null ? null : that.step.map(t -> (JCTree.JCExpressionStatement) t.clone());
    super.visitForLoop(that);
  }
  @Override
  public void visitForeachLoop(JCTree.JCEnhancedForLoop that) {
    that.body = that.body == null ? null : (JCTree.JCStatement) that.body.clone();
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    that.var = that.var == null ? null : (JCTree.JCVariableDecl) that.var.clone();
    super.visitForeachLoop(that);
  }
  @Override
  public void visitLabelled(JCTree.JCLabeledStatement that)   {
    that.body = that.body == null ? null : (JCTree.JCStatement) that.body.clone();
    super.visitLabelled(that);
  }
  @Override
  public void visitSwitch(JCTree.JCSwitch that)               {
    that.cases = that.cases == null ? null : that.cases.map(t -> (JCTree.JCCase) t.clone());
    that.selector = that.selector == null ? null : (JCTree.JCExpression) that.selector.clone();
    super.visitSwitch(that);
  }
  @Override
  public void visitCase(JCTree.JCCase that)                   {
    //that.body = that.body == null ? null : (JCTree) that.body.clone();
    that.stats = that.stats == null ? null : that.stats.map(t -> (JCTree.JCStatement) t.clone());
    //that.labels = that.labels == null ? null : that.labels.map(t -> (JCTree.JCCaseLabel) t.clone());
    super.visitCase(that);
  }
  /*@Override
  public void visitSwitchExpression(JCTree.JCSwitchExpression that)               {
    that.selector = that.selector == null ? null : (JCTree.JCExpression) that.selector.clone();
    that.cases = that.cases == null ? null : that.cases.map(t -> (JCTree.JCCase) t.clone());
    super.visitSwitchExpression(that);
  }*/
  @Override
  public void visitSynchronized(JCTree.JCSynchronized that)   {
    that.body = that.body == null ? null : (JCTree.JCBlock) that.body.clone();
    that.lock = that.lock == null ? null : (JCTree.JCExpression) that.lock.clone();
    super.visitSynchronized(that);
  }
  @Override
  public void visitTry(JCTree.JCTry that)                     {
    that.body = that.body == null ? null : (JCTree.JCBlock) that.body.clone();
    that.finalizer = that.finalizer == null ? null : (JCTree.JCBlock) that.finalizer.clone();
    that.catchers = that.catchers == null ? null : that.catchers.map(t -> (JCTree.JCCatch) t.clone());
    that.resources = that.resources == null ? null : that.resources.map(t -> (JCTree) t.clone());
    super.visitTry(that);
  }
  @Override
  public void visitCatch(JCTree.JCCatch that)                 {
    that.body = that.body == null ? null : (JCTree.JCBlock) that.body.clone();
    that.param = that.param == null ? null : (JCTree.JCVariableDecl) that.param.clone();
    super.visitCatch(that);
  }
  @Override
  public void visitConditional(JCTree.JCConditional that)     {
    that.cond = that.cond == null ? null : (JCTree.JCExpression) that.cond.clone();
    that.falsepart = that.falsepart == null ? null : (JCTree.JCExpression) that.falsepart.clone();
    that.truepart = that.truepart == null ? null : (JCTree.JCExpression) that.truepart.clone();
    super.visitConditional(that);
  }
  @Override
  public void visitIf(JCTree.JCIf that)                       {
    that.cond = that.cond == null ? null : (JCTree.JCExpression) that.cond.clone();
    that.thenpart = that.thenpart == null ? null : (JCTree.JCStatement) that.thenpart.clone();
    that.elsepart = that.elsepart == null ? null : (JCTree.JCStatement) that.elsepart.clone();
    super.visitIf(that);
  }
  @Override
  public void visitExec(JCTree.JCExpressionStatement that)    {
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    super.visitExec(that);
  }
  @Override
  public void visitBreak(JCTree.JCBreak that)                 {
    that.target = that.target == null ? null : (JCTree) that.target.clone();
    super.visitBreak(that);
  }
  /*@Override
  public void visitYield(JCTree.JCYield that)                 {
    that.value = that.value == null ? null : (JCTree.JCExpression) that.value.clone();
    that.target = that.target == null ? null : (JCTree) that.target.clone();
    super.visitYield(that);
  }*/
  @Override
  public void visitContinue(JCTree.JCContinue that)           {
    that.target = that.target == null ? null : (JCTree) that.target.clone();
    super.visitContinue(that);
  }
  @Override
  public void visitReturn(JCTree.JCReturn that)               {
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    super.visitReturn(that);
  }
  @Override
  public void visitThrow(JCTree.JCThrow that)                 {
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    super.visitThrow(that);
  }
  @Override
  public void visitAssert(JCTree.JCAssert that)               {
    that.cond = that.cond == null ? null : (JCTree.JCExpression) that.cond.clone();
    that.detail = that.detail == null ? null : (JCTree.JCExpression) that.detail.clone();
    super.visitAssert(that);
  }
  @Override
  public void visitApply(JCTree.JCMethodInvocation that)      {
    that.args = that.args == null ? null : that.args.map(t -> (JCTree.JCExpression) t.clone());
    that.meth = that.meth == null ? null : (JCTree.JCExpression) that.meth.clone();
    that.typeargs = that.typeargs == null ? null : that.typeargs.map(t -> (JCTree.JCExpression) t.clone());
    super.visitApply(that);
  }
  @Override
  public void visitNewClass(JCTree.JCNewClass that)           {
    that.args = that.args == null ? null : that.args.map(t -> (JCTree.JCExpression) t.clone());
    that.typeargs = that.typeargs == null ? null : that.typeargs.map((t -> (JCTree.JCExpression) t.clone()));
    that.clazz = that.clazz == null ? null : (JCTree.JCExpression) that.clazz.clone();
    that.def = that.def == null ? null : (JCTree.JCClassDecl) that.def.clone();
    that.encl = that.encl == null ? null : (JCTree.JCExpression) that.encl.clone();
    super.visitNewClass(that);
  }
  @Override
  public void visitNewArray(JCTree.JCNewArray that)           {
    that.annotations = that.annotations == null ? null : that.annotations.map(t -> (JCTree.JCAnnotation) t.clone());
    that.dimAnnotations = that.dims == null ? null : that.dimAnnotations.map(l -> l.map(t -> (JCTree.JCAnnotation) t.clone()));
    that.dims = that.dims == null ? null : that.dims.map(t -> (JCTree.JCExpression) t.clone());
    that.elems = that.elems == null ? null : that.elems.map(t -> (JCTree.JCExpression) t.clone());
    that.elemtype = that.elemtype == null ? null : (JCTree.JCExpression) that.elemtype.clone();
    super.visitNewArray(that);
  }
  @Override
  public void visitLambda(JCTree.JCLambda that)               {
    that.body = that.body == null ? null : (JCTree) that.body.clone();
    that.params = that.params == null ? null : that.params.map(t -> (JCTree.JCVariableDecl) t.clone());
    super.visitLambda(that);
  }
  @Override
  public void visitParens(JCTree.JCParens that)               {
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    super.visitParens(that);
  }
  @Override
  public void visitAssign(JCTree.JCAssign that)               {
    that.lhs = that.lhs == null ? null : (JCTree.JCExpression) that.lhs.clone();
    that.rhs = that.rhs == null ? null : (JCTree.JCExpression) that.rhs.clone();
    super.visitAssign(that);
  }
  @Override
  public void visitAssignop(JCTree.JCAssignOp that)           {
    that.lhs = that.lhs == null ? null : (JCTree.JCExpression) that.lhs.clone();
    that.rhs = that.rhs == null ? null : (JCTree.JCExpression) that.rhs.clone();
    super.visitAssignop(that);
  }
  @Override
  public void visitUnary(JCTree.JCUnary that)                 {
    that.arg = that.arg == null ? null : (JCTree.JCExpression) that.arg.clone();
    super.visitUnary(that);
  }
  @Override
  public void visitBinary(JCTree.JCBinary that)               {
    that.lhs = that.lhs == null ? null : (JCTree.JCExpression) that.lhs.clone();
    that.rhs = that.rhs == null ? null : (JCTree.JCExpression) that.rhs.clone();
    super.visitBinary(that);

  }
  @Override
  public void visitTypeCast(JCTree.JCTypeCast that)           {
    that.clazz = that.clazz == null ? null : (JCTree) that.clazz.clone();
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    super.visitTypeCast(that);
  }
  @Override
  public void visitTypeTest(JCTree.JCInstanceOf that)         {
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    //that.pattern = that.pattern == null ? null : (JCTree) that.pattern.clone();
    super.visitTypeTest(that);
  }
  /*@Override
  public void visitBindingPattern(JCTree.JCBindingPattern that) {
    that.var = that.var == null ? null : (JCTree.JCVariableDecl) that.var.clone();
    super.visitBindingPattern(that);
  }*/
  /*@Override
  public void visitDefaultCaseLabel(JCTree.JCDefaultCaseLabel that) {
    super.visitDefaultCaseLabel(that);
  }*/
  /*@Override
  public void visitParenthesizedPattern(JCTree.JCParenthesizedPattern that) {
    that.pattern = that.pattern == null ? null : (JCTree.JCPattern) that.pattern.clone();
    super.visitParenthesizedPattern(that);
  }*/
  /*@Override
  public void visitGuardPattern(JCTree.JCGuardPattern that) {
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    that.patt = that.patt == null ? null : (JCTree.JCPattern) that.patt.clone();
    super.visitGuardPattern(that);
  }*/
  @Override
  public void visitIndexed(JCTree.JCArrayAccess that)         {
    that.index = that.index == null ? null : (JCTree.JCExpression) that.index.clone();
    that.indexed = that.indexed == null ? null : (JCTree.JCExpression) that.indexed.clone();
    super.visitIndexed(that);
  }
  @Override
  public void visitSelect(JCTree.JCFieldAccess that)          {
    that.selected = that.selected == null ? null : (JCTree.JCExpression) that.selected.clone();
    super.visitSelect(that);
  }
  @Override
  public void visitReference(JCTree.JCMemberReference that)   {
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    that.typeargs = that.typeargs == null ? null : that.typeargs.map(t -> (JCTree.JCExpression) t.clone());
    super.visitReference(that);
  }
  @Override
  public void visitIdent(JCTree.JCIdent that)                 {
    super.visitIdent(that);
  }
  @Override
  public void visitLiteral(JCTree.JCLiteral that)             {
    super.visitLiteral(that);
  }
  @Override
  public void visitTypeIdent(JCTree.JCPrimitiveTypeTree that) {
    super.visitTypeIdent(that);
  }
  @Override
  public void visitTypeArray(JCTree.JCArrayTypeTree that)     {
    that.elemtype = that.elemtype == null ? null : (JCTree.JCExpression) that.elemtype.clone();
    super.visitTypeArray(that);
  }
  @Override
  public void visitTypeApply(JCTree.JCTypeApply that)         {
    that.clazz = that.clazz == null ? null : (JCTree.JCExpression) that.clazz.clone();
    that.arguments = that.arguments == null ? null : that.arguments.map(t -> (JCTree.JCExpression) t.clone());
    super.visitTypeApply(that);
  }
  @Override
  public void visitTypeUnion(JCTree.JCTypeUnion that)         {
    that.alternatives = that.alternatives == null ? null : that.alternatives.map(t -> (JCTree.JCExpression) t.clone());
    super.visitTypeUnion(that);
  }
  @Override
  public void visitTypeIntersection(JCTree.JCTypeIntersection that)  {
    that.bounds = that.bounds == null ? null : that.bounds.map(t -> (JCTree.JCExpression) t.clone());
    super.visitTypeIntersection(that);
  }
  @Override
  public void visitTypeParameter(JCTree.JCTypeParameter that) {
    that.annotations = that.annotations == null ? null : that.annotations.map(t -> (JCTree.JCAnnotation) t.clone());
    that.bounds = that.bounds == null ? null : that.bounds.map(t -> (JCTree.JCExpression) t.clone());
    super.visitTypeParameter(that);
  }
  @Override
  public void visitWildcard(JCTree.JCWildcard that)           {
    that.inner = that.inner == null ? null : (JCTree) that.inner.clone();
    super.visitWildcard(that);
  }
  @Override
  public void visitTypeBoundKind(JCTree.TypeBoundKind that)   {
    super.visitTypeBoundKind(that);
  }
  @Override
  public void visitAnnotation(JCTree.JCAnnotation that)       {
    that.annotationType = that.annotationType == null ? null : (JCTree) that.annotationType.clone();
    that.args = that.args == null ? null : that.args.map(t -> (JCTree.JCExpression) t.clone());
    super.visitAnnotation(that);
  }
  @Override
  public void visitModifiers(JCTree.JCModifiers that)         {
    that.annotations = that.annotations == null ? null : that.annotations.map(t -> (JCTree.JCAnnotation) t.clone());
    super.visitModifiers(that);
  }
  @Override
  public void visitAnnotatedType(JCTree.JCAnnotatedType that) {
    that.annotations = that.annotations == null ? null : that.annotations.map(t -> (JCTree.JCAnnotation) t.clone());
    that.underlyingType = that.underlyingType == null ? null : (JCTree.JCExpression) that.underlyingType.clone();
    super.visitAnnotatedType(that);
  }
  @Override
  public void visitErroneous(JCTree.JCErroneous that)         {
    that.errs = that.errs == null ? null : that.errs.map(t -> (JCTree) t.clone());
    super.visitErroneous(that);
  }
  @Override
  public void visitModuleDef(JCTree.JCModuleDecl that)        {
    that.mods = that.mods == null ? null : (JCTree.JCModifiers) that.mods.clone();
    that.qualId = that.qualId == null ? null : (JCTree.JCExpression) that.qualId.clone();
    that.directives = that.directives == null ? null : that.directives.map(t -> (JCTree.JCDirective) t.clone());
    super.visitModuleDef(that);
  }
  @Override
  public void visitExports(JCTree.JCExports that)             {
    that.qualid = that.qualid == null ? null : (JCTree.JCExpression) that.qualid.clone();
    that.moduleNames = that.moduleNames == null ? null : that.moduleNames.map(t -> (JCTree.JCExpression) t.clone());
    super.visitExports(that);
  }
  @Override
  public void visitOpens(JCTree.JCOpens that)                 {
    that.qualid = that.qualid == null ? null : (JCTree.JCExpression) that.qualid.clone();
    that.moduleNames = that.moduleNames == null ? null : that.moduleNames.map(t -> (JCTree.JCExpression) t.clone());
    super.visitOpens(that);
  }
  @Override
  public void visitProvides(JCTree.JCProvides that)           {
    that.implNames = that.implNames == null ? null : that.implNames.map(t -> (JCTree.JCExpression) t.clone());
    that.serviceName = that.serviceName == null ? null : (JCTree.JCExpression) that.serviceName.clone();
    super.visitProvides(that);
  }
  @Override
  public void visitRequires(JCTree.JCRequires that)           {
    that.moduleName = that.moduleName == null ? null : (JCTree.JCExpression) that.moduleName.clone();
    super.visitRequires(that);
  }
  @Override
  public void visitUses(JCTree.JCUses that)                   {
    that.qualid = that.qualid == null ? null : (JCTree.JCExpression) that.qualid.clone();
    super.visitUses(that);
  }
  @Override
  public void visitLetExpr(JCTree.LetExpr that)               {
    that.expr = that.expr == null ? null : (JCTree.JCExpression) that.expr.clone();
    that.defs = that.defs == null ? null : that.defs.map(t -> (/*JCTree.JCStatement*/ JCTree.JCVariableDecl) t.clone());
    super.visitLetExpr(that);
  }
}
