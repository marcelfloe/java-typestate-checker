package jatyc.key;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import jatyc.typestate.graph.State;
import jatyc.utils.ClassUtils;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class CommonPrinterFeatures extends Pretty {

  public CommonPrinterFeatures(Writer out, boolean sourceOutput) {
    super(out, sourceOutput);
  }

  //@State does not exist, @Ensures is used instead
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
      case "Requires", "Ensures" -> {/* no comments required as the visitMethodDef-method takes care of the typestate information */}
      case "Typestate" -> {/* no comment required as the typestate checker takes care of this */}
      default -> super.visitAnnotation(tree);
    }
  }

  @Override
  public void visitImport(JCTree.JCImport tree) {
    if (tree.toString().matches(".+jatyc\\.lib.+\\r\\n")) {
      return;
    }
    super.visitImport(tree);
  }

  protected void printTypestateAnnotationInformation(JCTree.JCMethodDecl tree, ClassUtils utils) {
    try {
      Type treeType = tree.type;
      if (treeType != null && utils.hasProtocol(treeType)) {
        List<State> statesList = utils.getGraph(tree.type).getAllConcreteStates().stream().toList();

        for (JCTree.JCAnnotation annotation : tree.mods.annotations) {
          String type = annotation.annotationType.toString();
          if (type.equals("Ensures")) { //the @Ensures annotation is used for return types as well, instead of @State
            List<String> stateName = getValueOnly(annotation.args.head);
            long stateId = getStateIndex(stateName.get(0), statesList);
            if (stateId == -1) continue; //state doesn't exist
            printStateAnnotation(stateId);
          }
        }
      }

      for (JCTree.JCVariableDecl varDecl : tree.params) {
        if (varDecl.type == null) {
          continue;
        }

        boolean protocolExists = utils.hasProtocol(varDecl.type);
        if (protocolExists) {
          List<State> statesList = utils.getGraph(varDecl.type).getAllConcreteStates().stream().toList();

          for (JCTree.JCAnnotation annotation : varDecl.mods.annotations) {
            String type = annotation.annotationType.toString();
            if (type.equals("Ensures")) {
              List<String> stateName = getValueOnly(annotation.args.head);
              long stateId = getStateIndex(stateName.get(0), statesList);
              if (stateId == -1) continue; //state doesn't exist
              printEnsuresAnnotation(stateId, getParamName(varDecl), getParamClass(varDecl));

            } else if (type.equals("Requires")) {
              List<String> stateName = getValueOnly(annotation.args.head);
              List<Long> stateIds = new ArrayList<>(stateName.size());
              for (String s : stateName) {
                long stateId = getStateIndex(s, statesList);
                if (stateId == -1) continue; //state doesn't exist
                stateIds.add(stateId);
              }
              printRequiresAnnotation(stateIds, getParamName(varDecl), getParamClass(varDecl));
            }
          }
        }
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  protected List<String> getValueOnly(JCTree tree) throws IOException {
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

  protected void printStateAnnotation(long state) throws IOException {
    print("//@ ensures \\result.state == " + state + ";\n");
  }

  protected void printEnsuresAnnotation(long state, String paramName, String paramClass) throws IOException {
    printEnsuresComment(paramName + "." + paramClass + "State == " + state);
  }

  protected void printRequiresAnnotation(List<Long> state, String paramName, String paramClass) throws IOException {
    List<String> equations = new ArrayList<>();
    for (long l : state) {
      equations.add("%s.%sState == %s".formatted(paramName, paramClass, l));
    }

    printRequiresComment(getOr(equations));
  }

  protected void printEnsuresComment(String comment) throws IOException {
    print("\n//@ ensures " + comment + ";");
  }

  protected void printRequiresComment(String comment) throws IOException {
    print("\n//@ requires " + comment + ";");
  }

  protected void printAssignableComment(String comment) throws IOException {
    print("\n//@ assignable " + comment + ";");
  }

  protected String getOr(List<String> list) {
    StringBuilder sb = new StringBuilder();
    if (list.isEmpty()) return sb.toString();
    sb.append(list.get(0));
    for (int i = 1; i < list.size(); i++) {
      sb.append(" || ").append(list.get(i));
    }
    return sb.toString();
  }

  protected String getParamName(JCTree.JCVariableDecl varDecl) {
    return varDecl.sym.toString();
  }

  protected String getParamClass(JCTree.JCVariableDecl varDecl) {
    return varDecl.vartype.toString();
  }

  protected long getStateIndex(String state, List<State> states) {
    List<State> actualState = states.stream().filter(s -> s.getName().equals(state)).toList();
    if (actualState.size() != 1) {
      return -1;
    } else {
      return actualState.get(0).getId();
    }
  }
}
