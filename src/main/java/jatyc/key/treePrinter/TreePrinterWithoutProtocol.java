package jatyc.key.treePrinter;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import jatyc.JavaTypestateChecker;
import jatyc.core.JavaType;
import jatyc.key.contracts.ContractLog;
import jatyc.key.treeUtils.SubtypesLog;
import jatyc.typestate.graph.State;

import java.io.IOException;
import java.io.Writer;
import java.util.*;

/**
 * This class prints a version of the given tree that does not include any protocol information of this-pointers,
 * but all typestate information based on annotations.
 */
public class TreePrinterWithoutProtocol extends CommonPrinterFeatures {

  private final Stack<Set<LocalVar>> localVars = new Stack<>();
  private boolean insideMethod = false;

  public TreePrinterWithoutProtocol(Writer out, boolean sourceOutput, JavaTypestateChecker checker, ContractLog contractLog, SubtypesLog subtypes) {
    super(out, sourceOutput, checker, contractLog, subtypes);
  }

  //annotations and imports are managed by super class


  @Override
  public void visitClassDef(JCTree.JCClassDecl tree) {
    boolean temp = insideMethod;
    insideMethod = false;
    super.visitClassDef(tree);
    insideMethod = temp;
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    boolean temp = insideMethod;
    insideMethod = true;
    printTypestateInformationWithoutProtocol(tree);
    super.visitMethodDef(tree);
    insideMethod = temp;
  }

  @Override
  public void visitVarDef(JCTree.JCVariableDecl tree) {
    if (!localVars.empty()) localVars.peek().add(new LocalVar(tree.sym.toString(), tree.type));
    super.visitVarDef(tree);
  }

  @Override
  public void visitBlock(JCTree.JCBlock tree) {
    if (!insideMethod) {
      super.visitBlock(tree);
      return;
    }

    localVars.push(new HashSet<>());
    if (tree.stats.last() instanceof JCTree.JCReturn) {
      super.visitBlock(tree);
    } else {
      try {
        printFlags(tree.flags);
        printBlockWithAssertion(tree.stats);
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }
    localVars.pop();
  }

  public void printBlockWithAssertion(com.sun.tools.javac.util.List<? extends JCTree> stats) throws IOException { //copy from Pretty, but with inserted assertion
    print("{");
    println();
    printStats(stats);
    printAssertion(localVars.peek());
    print("}");
  }

  @Override
  public void visitReturn(JCTree.JCReturn tree) {
    if (tree.expr == null || tree.expr instanceof JCTree.JCLiteral) { //empty return/returning null -> return;/return null;
      //all local variables need to be checked for protocol completion
      try {
        printAssertion(getAllLocalVars());
        super.visitReturn(tree);
      } catch (IOException e) {
        throw new RuntimeException(e);
      }

    } else if (tree.expr instanceof JCTree.JCIdent returnedVar) { //return with variable name -> return a;
      //all local variables except the returned one need to be checked for protocol completion

      Set<LocalVar> localVarSet = getAllLocalVars();
      localVarSet.remove(new LocalVar(returnedVar.name.toString(), returnedVar.type));

      try {
        printAssertion(localVarSet);
        super.visitReturn(tree);
      } catch (IOException e) {
        throw new RuntimeException(e);
      }

    } else { //return with method call/new Value -> return foo();/return new A();
      //all local variables need to be checked for protocol completion
      //also a temp variable is required to move the call in front of the return statement

      String tempVarName = "temp" + UUID.randomUUID().toString().replaceAll("-", "");
      Type expressionType = tree.expr.type.baseType();

      try {
        print(expressionType + " " + tempVarName + " = ");
        printExpr(tree.expr);
        print(";\n");
        printAssertion(getAllLocalVars());
        print("return " + tempVarName + ";");
      } catch (IOException e) {
        throw new RuntimeException(e);
      }

    }
  }

  private void printAssertion(Collection<LocalVar> localVars) throws IOException {
    String assertion = getAssertion(localVars);
    if (!assertion.isBlank()) print("/*@ assert " + assertion +";*/\n");
  }

  private String getAssertion(Collection<LocalVar> localVars ) {
    StringBuilder assertion = new StringBuilder();
    for (LocalVar localVar : localVars) {
      if (localVar.type == null) continue;
      JavaType javaType = checker.getUtils().typeIntroducer.getJavaType(localVar.type);
      Set<JavaType> types = getSuperTypes(javaType);
      types.add(javaType);

      for(JavaType type : types) {
        if (type.hasProtocol()) {
          StringBuilder endStates = new StringBuilder();
          List<Long> droppableStates = getDroppableStateIDs(type.getGraph().getAllConcreteStates());
          droppableStates.add(type.getGraph().getEndState().getId());
          for (long droppableState : droppableStates) {
            if (!endStates.isEmpty()) endStates.append(" || ");
            endStates.append(localVar.name).append(".").append(type).append("State == ").append(droppableState);
          }
          if (!assertion.isEmpty()) assertion.append(" && ");
          assertion.append("(").append(endStates).append(")");
        }
      }
    }
    return assertion.toString();
  }

  private List<Long> getDroppableStateIDs(Collection<State> states) {
    List<Long> droppableStateIDs = new ArrayList<>();
    for (State state : states) {
      if (state.canDropHere()) droppableStateIDs.add(state.getId());
    }
    return droppableStateIDs;
  }

  private Set<LocalVar> getAllLocalVars() {
    return localVars.stream().reduce(new HashSet<>(), (set1, set2) -> {set1.addAll(set2); return set1;});
  }

  private Set<JavaType> getSuperTypes(JavaType type) {
    Set<JavaType> superTypes = new HashSet<>();
    for (JavaType superType : type.getSuperTypes()) {
      superTypes.add(superType);
      superTypes.addAll(getSuperTypes(superType));
    }
    return superTypes;
  }

  private record LocalVar(String name, Type type) {}

}
