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
public class TreePrinterWithoutProtocol extends Pretty {
  private JavaTypestateChecker checker;
  private Writer out;

  public TreePrinterWithoutProtocol(Writer out, boolean sourceOutput, JavaTypestateChecker checker) {
    super(out, sourceOutput);
    this.checker = checker;
    this.out = out;
  }

  //TODO: @State does not exist, @Ensures is used instead
  @Override
  public void visitAnnotation(JCTree.JCAnnotation tree) {
    switch (tree.annotationType.toString()) {
      case "JML" -> {
        try {
          print("/*@ ");
          print(getValueOnly(tree.args.head).get(0));
          print(" */");
        } catch (IOException e) {
          throw new RuntimeException(e);
        }
      }
      case "Nullable" -> {
        try {
          print("/*@ nullable */");
        } catch (IOException e) {
          throw new RuntimeException(e);
        }
      }
      case "State", "Requires", "Ensures" -> {/* no comments required as the visitMethodDef-method takes care of the typestate information */}
      case "Typestate" -> {
        //TODO: implement correct comments (probably no comment required?)
        //TODO: get Typestate information
      }
      default -> super.visitAnnotation(tree);
    }
  }

  @Override
  public void visitImport(JCTree.JCImport tree) {
    //System.out.println("*************");
    //System.out.println(tree);
    JCTree qualid = tree.qualid;
    /*System.out.println(qualid.getClass());
    if (qualid instanceof JCTree.JCFieldAccess) {
      System.out.println("+++++");
      System.out.println(qualid.type);
      System.out.println(((JCTree.JCFieldAccess) qualid).sym);
      System.out.println(((JCTree.JCFieldAccess) qualid).name);
      System.out.println(((JCTree.JCFieldAccess) qualid).selected);
      System.out.println("+++++");
    }
    //System.out.println("*************");
    //System.out.println(tree);*/
    if (tree.toString().matches(".+jatyc\\.lib.+\\r\\n")) {
      //System.out.println("SKIPPED");
      return;
    }
    super.visitImport(tree);
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    /*System.out.println("--||||||||||||||||||||||||||||||||||||||||--");
    System.out.println(tree.name);
    System.out.println(tree.sym);
    System.out.println(tree.restype);
    System.out.println(tree.type);
    System.out.println("--||||||||||||||||||||||||||||||||||||||||--");*/
    ClassUtils utils = checker.getUtils().classUtils;
    //System.out.println(tree);
    try {
      Type treeType = tree.type;
      print("+++++" + treeType + "+++++");
      if (treeType != null && utils.hasProtocol(treeType)) {
        List<String> statesList = utils.getGraph(tree.type).getAllConcreteStates().stream().map(State::getName).toList();
        for (JCTree.JCAnnotation annotation : tree.mods.annotations) {
          String type = annotation.annotationType.toString();
          if (type.equals("Ensures")) { //the @Ensures annotation is used for return types as well, instead of @State
            List<String> state = getValueOnly(annotation.args.head);
            int stateIndex = getStateIndex(state.get(0), statesList);
            printStateAnnotation(stateIndex);
            //print(AnnotationTypes.ENSURES + "ANNOTATION");
          }
        }
      }
      for (JCTree.JCVariableDecl varDecl : tree.params) {
        if (varDecl.type == null) {
          continue;
        }
        String paramName = getParamName(varDecl);
        boolean protocolExists = utils.hasProtocol(varDecl.type);
        if (protocolExists) {
          List<String> statesList = utils.getGraph(varDecl.type).getAllConcreteStates().stream().map(State::getName).toList();
          for (JCTree.JCAnnotation annotation : varDecl.mods.annotations) {
            /*System.out.println("++||||||||||||||||||||||||||||||||||||||||++");
            System.out.println(varDecl.name);
            System.out.println(varDecl.sym);
            System.out.println(varDecl.vartype);
            System.out.println(varDecl.type);
            System.out.println("++||||||||||||||||||||||||||||||||||||||||++");*/
            String type = annotation.annotationType.toString();
            if (type.equals("Ensures")) { //TODO: implement correct comments
              List<String> state = getValueOnly(annotation.args.head);
              int stateIndex = getStateIndex(state.get(0), statesList);
              printEnsuresAnnotation(stateIndex, paramName);
              //print(AnnotationTypes.ENSURES + "DECLARATION");
            } else if (type.equals("Requires")) { //TODO: implement correct comments
              List<String> state = getValueOnly(annotation.args.head);
              //System.out.println(state + "---" + statesList);
              List<Integer> stateIndex = new ArrayList<>(state.size());
              for (String s : state) {
                stateIndex.add(getStateIndex(s, statesList));
              }
              printRequiresAnnotation(stateIndex, paramName);
              //print(AnnotationTypes.REQUIRES + "DECLARATION");
            }
          }
        }
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }

    super.visitMethodDef(tree);
  }

  private List<String> getValueOnly(JCTree tree) throws IOException {
    if (tree instanceof JCTree.JCAssign) {
      JCTree rightTree = ((JCTree.JCAssign) tree).rhs;
      if (rightTree instanceof JCTree.JCLiteral) {
        return List.of((((JCTree.JCLiteral) rightTree).value).toString());
      } else if (rightTree instanceof JCTree.JCNewArray) {
        List<String> value = new ArrayList<>();
        for (JCTree.JCExpression elem : ((JCTree.JCNewArray) rightTree).elems) {
          if (elem  instanceof JCTree.JCLiteral) {
            value.add(((JCTree.JCLiteral) elem).value.toString());
          }
        }
        return value;
      }
    }
    return null;
  }

  private void printStateAnnotation(int state) throws IOException {
    print("//@ ensures \\result.state == " + state + ";\n");
  }

  private void printEnsuresAnnotation(int state, String paramName) throws IOException {
    print("//@ ensures " + paramName + ".state == " + state + ";\n");
  }

  private void printRequiresAnnotation(List<Integer> state, String paramName) throws IOException {
    StringBuilder sb = new StringBuilder();
    sb.append("//@ requires ");
    sb.append(paramName).append(".state == ").append(state.get(0));
    for (int i = 1; i < state.size(); i++) {
      sb.append(" || ");
      sb.append(paramName).append(".state == ").append(state.get(i));
    }
    sb.append(";\n");
    print(sb.toString());
  }

  private String getParamName(JCTree.JCVariableDecl varDecl) {
    return varDecl.sym.toString();
  }

  private int getStateIndex(String state, List<String> states) {
    return switch (state) {
      case "end" -> -1;
      case "unknown" -> -2;
      case "bottom" -> -3;
      case "moved" -> -4;
      case "primitive" -> -5;
      case "noProtocol" -> -6;
      case "null" -> -7;
      case "object" -> -8;
      default -> states.indexOf(state);
    };
  }
}
