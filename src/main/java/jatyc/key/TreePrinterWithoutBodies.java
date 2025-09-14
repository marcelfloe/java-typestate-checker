package jatyc.key;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.util.Name;
import jatyc.JavaTypestateChecker;
import jatyc.util.multimap.BiMap;
import jatyc.util.multimap.QuadMap;
import jatyc.typestate.graph.DecisionState;
import jatyc.typestate.graph.Graph;
import jatyc.typestate.graph.State;
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
public class TreePrinterWithoutBodies extends Pretty {
  private JavaTypestateChecker checker;
  private Type enclClassType;
  private String ghostVar;

  public TreePrinterWithoutBodies(Writer out, boolean sourceOutput, JavaTypestateChecker checker) {
    super(out, sourceOutput);
    this.checker = checker;
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
  public void visitClassDef(JCTree.JCClassDecl tree) {
    Type prevClassType = enclClassType;
    enclClassType = tree.type;
    String prevGhostVar = ghostVar;
    ghostVar = tree.getSimpleName().toString() + "State";
    if (tree.type != null && checker.getUtils().classUtils.hasProtocol(tree.type)) {
      try {
        print("//@ public ghost int " + ghostVar + " = -1;\n");
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }
    super.visitClassDef(tree);
    enclClassType = prevClassType;
    ghostVar = prevGhostVar;
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    ClassUtils utils = checker.getUtils().classUtils;

    printTypestateAnnotationInformation(tree, utils); //prints typestate information based on @Ensures and @Requires
    printProtocolInformation(tree, utils); //prints typestate information based on protocol of "this"-class

    JCTree.JCMethodDecl treeClone = (JCTree.JCMethodDecl) tree.clone();
    treeClone.body = null; //KeY uses method stubs without body

    super.visitMethodDef(treeClone);
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

  private void printStateAnnotation(long state) throws IOException {
    print("//@ ensures \\result.state == " + state + ";\n");
  }

  private void printEnsuresAnnotation(long state, String paramName, String paramClass) throws IOException {
    printEnsuresComment(paramName + "." + paramClass + "State == " + state);
  }

  private void printRequiresAnnotation(List<Long> state, String paramName, String paramClass) throws IOException {
    List<String> equations = new ArrayList<>();
    for (long l : state) {
      equations.add("%s.%sState == %s".formatted(paramName, paramClass, l));
    }

    printRequiresComment(getOr(equations));
  }

  private void printEnsuresComment(String comment) throws IOException {
    print("\n//@ ensures " + comment + ";");
  }

  private void printRequiresComment(String comment) throws IOException {
    print("\n//@ requires " + comment + ";");
  }

  private void printAssignableComment(String comment) throws IOException {
    print("\n//@ assignable " + comment + ";");
  }

  private String getOr(List<String> list) {
    StringBuilder sb = new StringBuilder();
    if (list.isEmpty()) return sb.toString();
    sb.append(list.get(0));
    for (int i = 1; i < list.size(); i++) {
      sb.append(" || ").append(list.get(i));
    }
    return sb.toString();
  }

  private String getParamName(JCTree.JCVariableDecl varDecl) {
    return varDecl.sym.toString();
  }

  private String getParamClass(JCTree.JCVariableDecl varDecl) {
    return varDecl.vartype.toString();
  }

  private long getStateIndex(String state, List<State> states) {
    List<State> actualState = states.stream().filter(s -> s.getName().equals(state)).toList();
    if (actualState.size() != 1) {
      return -1;
    } else {
      return actualState.get(0).getId();
    }
  }

  private void printTypestateAnnotationInformation(JCTree.JCMethodDecl tree, ClassUtils utils) {
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

  private void printProtocolInformation(JCTree.JCMethodDecl tree, ClassUtils utils) {
    try {
      if (enclClassType == null || !utils.hasProtocol(enclClassType)) {
        return; //no protocol -> no information required
      }

      Graph graph = utils.getGraph(enclClassType);

      QuadMap<OriginalState, MethodName, ReturnedValue, NewState> quadMap = getAllMappings(graph);

      Name methodName = tree.name;
      String stateName = enclClassType + "State";
      if (methodName.toString().equals("<init>")) {
        printEnsuresComment(stateName + " == " + graph.getInitialState().getId());
      } else {
        Set<QuadMap.Entry<OriginalState, MethodName, ReturnedValue, NewState>> set = quadMap.getBMapping(new MethodName(methodName.toString()));
        if (set == null) return;
        List<String> originalStates = new ArrayList<>(set.size());
        for (QuadMap.Entry<OriginalState, MethodName, ReturnedValue, NewState> e : set) {
          originalStates.add(e.w().originalStateId);
          if (e.y() == null) {
            printEnsuresComment("\\old(" + stateName + ") == " + e.w().originalStateId + " ==> " + stateName + " == " + e.z().newStateId);
          } else {
            printEnsuresComment("(\\old(" + stateName + ") == " + e.w().originalStateId + " && \\result == " + e.y().returnedValue +") ==> " + stateName + " == " + e.z().newStateId);
          }
        }
        printRequiresComment(getOr(originalStates.stream().distinct().map(s -> stateName + " == " + s).toList()));
      }
      printAssignableComment(stateName);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  /**
   * This method creates a Map of all initial states and methods to the new state given the returned value.
   * If the transition between states is independent of the returned value, then the returned value is null.
   * @param graph the Graph containing the information about the transitions between states.
   * @return a QuadMap containing all transitions.
   */
  private QuadMap<OriginalState, MethodName, ReturnedValue, NewState> getAllMappings(Graph graph) {
    QuadMap<OriginalState, MethodName, ReturnedValue, NewState> quadMap = new QuadMap<>();

    Set<State> states = graph.getAllConcreteStates();

    BiMap<Long, State> statesMap = new BiMap();
    states.forEach(state -> statesMap.map(state.getId(), state));

    for (State state : states) {
      OriginalState originalState = new OriginalState(state.getId() + "");

      state.getTransitions().forEach((key, value) -> {
        String returnType = key.getReturnType().stringName();
        String methodName = key.getName();
        if (value instanceof DecisionState) {
          ((DecisionState) value).getTransitions().forEach((k,v) -> {
            if (returnType.equals("boolean")) { //-> boolean
              quadMap.map(originalState, new MethodName(methodName), new ReturnedValue(k.getLabel()), new NewState(v.getId() + ""));
            } else { //-> enum
              quadMap.map(originalState, new MethodName(methodName), new ReturnedValue(returnType + "." + k.getLabel()), new NewState(v.getId() + ""));
            }
          });
        } else if (value instanceof State) {
          quadMap.map(originalState, new MethodName(methodName), null, new NewState(((State) value).getId() + ""));
        } else {
          System.out.println("ERROR: " + value);
        }
      });
    }

    return quadMap;
  }

  private record OriginalState (String originalStateId) {}
  private record MethodName (String methodName) {}
  private record ReturnedValue (String returnedValue) {}
  private record NewState (String newStateId) {}
}
