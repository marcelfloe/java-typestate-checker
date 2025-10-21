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
 * This class prints a version of the given tree that does not include any protocol information,
 * but all typestate information based on annotations.
 * It also prints comments containing assertion for protocol completion.
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
  public void visitVarDef(JCTree.JCVariableDecl tree) { //logging local vars for protocol completion
    if (!localVars.empty()) localVars.peek().add(new LocalVar(tree.sym.toString(), tree.type));
    super.visitVarDef(tree);
  }

  @Override
  public void visitBlock(JCTree.JCBlock tree) {
    if (!insideMethod) {
      super.visitBlock(tree);
      return;
    }

    localVars.push(new HashSet<>()); //new name space for local vars
    if (tree.stats.last() instanceof JCTree.JCReturn) { //assertion handled by return statement
      super.visitBlock(tree);
    } else { //assertion at end of method body required
      try {
        printFlags(tree.flags);
        printBlockWithAssertion(tree.stats);
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }
    localVars.pop(); //removing the name space for local vars
  }

  public void printBlockWithAssertion(com.sun.tools.javac.util.List<? extends JCTree> stats) throws IOException { //copy from Pretty, but with inserted assertion
    print("{");
    println();
    printStats(stats);
    printAssertion(localVars.peek()); //assert protocol completion for all locals vars in this method body
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

  @Override
  public void visitContinue(JCTree.JCContinue tree) {
    try {
      printAssertion(localVars.peek()); //assertion for the protocol completion of local vars in this name space so far
      super.visitContinue(tree);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  @Override
  public void visitBreak(JCTree.JCBreak tree) {
    try {
      printAssertion(localVars.peek()); //assertion for the protocol completion of local vars in this name space so far
      super.visitBreak(tree);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  @Override
  public void visitAssign(JCTree.JCAssign tree) {
    JCTree.JCExpression lhs = tree.lhs;
    JavaType lhsType = checker.getUtils().typeIntroducer.getJavaType(lhs.type);
    if (!(lhs instanceof JCTree.JCFieldAccess) && lhsType.hasProtocol()) {
      //assigning a new value to a variable with protocol -> old value has to have finished its protocol
      String paramName = lhs.toString();
      try {
        printAssertion(List.of(new LocalVar(paramName, lhsType.getOriginal())));
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }

    JCTree.JCExpression rhs = tree.rhs;
    JavaType rhsType = checker.getUtils().typeIntroducer.getJavaType(rhs.type);
    if (lhs instanceof JCTree.JCFieldAccess && rhs instanceof JCTree.JCIdent && rhsType.hasProtocol()) {
      //assigning a new value with protocol to a field and value is a variable -> value has to have finished its protocol (shared type)
      String paramName = tree.rhs.toString();
      try {
        printAssertion(List.of(new LocalVar(paramName, rhsType.getOriginal())));
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }

    if (lhs instanceof JCTree.JCFieldAccess && rhs instanceof JCTree.JCMethodInvocation && rhsType.hasProtocol()) {
      //assigning a new value with protocol to a field and value is returned by method call
      // -> method call needs to be moved in front of assignment
      // -> returned value has to have finished its protocol (shared type)
      String paramName = "temp" + UUID.randomUUID().toString().replaceAll("-", "");
      try {
        print(rhsType + " " + paramName + " = " + rhs + ";\n");
        printAssertion(List.of(new LocalVar(paramName, rhsType.getOriginal())));
        print(lhs + " = " + paramName);
        return; //not printing the original assign statement
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }

    super.visitAssign(tree);
  }

  private void printAssertion(Collection<LocalVar> localVars) throws IOException {
    String assertion = getAssertion(localVars);
    if (!assertion.isBlank()) print("/*@ assert " + assertion +";*/\n");
  }

  //creates an assertion that all given local vars have finished their protocols
  private String getAssertion(Collection<LocalVar> localVars ) {
    StringBuilder assertion = new StringBuilder();
    for (LocalVar localVar : localVars) {
      if (localVar.type == null) continue;
      JavaType javaType = checker.getUtils().typeIntroducer.getJavaType(localVar.type);
      Set<JavaType> types = getSuperTypes(javaType);
      types.add(javaType);

      for(JavaType type : types) {
        if (type.hasProtocol()) {
          StringBuilder endStates = new StringBuilder().append(localVar.name).append(" == null");
          List<Long> droppableStates = getDroppableStateIDs(type.getGraph().getAllConcreteStates());
          for (long droppableState : droppableStates.stream().distinct().toList()) {
            endStates.append(" || ").append(localVar.name).append(".").append(type).append("State == ").append(droppableState);
          }
          if (!assertion.isEmpty()) assertion.append(" && ");
          assertion.append("(").append(endStates).append(")");
        }
      }
    }
    return assertion.toString();
  }

  //gets the IDs of all states in the given collection, which are droppable
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
