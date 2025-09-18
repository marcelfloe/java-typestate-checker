package jatyc.key;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import jatyc.typestate.graph.DecisionState;
import jatyc.typestate.graph.Graph;
import jatyc.typestate.graph.State;
import jatyc.util.multimap.BiMap;
import jatyc.util.multimap.QuadMap;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
//TODO: Include contracts of parent classes
//TODO: include subtyping in contracts

/**
 * This class prints a version of the given tree that does not include any method bodies,
 * but does include the protocol information of this-pointers and all typestate information based on annotations.
 */
public class CommonPrinterFeatures extends Pretty {
  protected Type enclClassType;
  protected Map<MethodSignature, MethodInformation> contracts = new HashMap<>();
  protected ContractLog contractLog;

  public CommonPrinterFeatures(Writer out, boolean sourceOutput, ContractLog contractLog) {
    super(out, sourceOutput);
    this.contractLog = contractLog;
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
    if (tree.toString().matches(".+jatyc\\.lib.+\\r\\n")) { //removes any imports for typestate checker annotations
      return;
    }
    super.visitImport(tree);
  }

  protected void printTypestateInformationWithoutProtocol(JCTree.JCMethodDecl tree) {
    String contract = getContract(new MethodSignature(enclClassType + "", tree.name + "", tree.params.stream().map(t -> t.type + "").toList()), false);
    try {
      print(contract);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  protected void printTypestateInformationWithProtocol(JCTree.JCMethodDecl tree)  {
    String contract = getContract(new MethodSignature(enclClassType + "", tree.name + "", tree.params.stream().map(t -> t.type + "").toList()), true);
    try {
      print(contract);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }

  }

  protected String getContract(MethodSignature signature, boolean withProtocolInformation) {
    List<String> requires = new ArrayList<>();
    List<String> ensures = new ArrayList<>();
    List<String> assignable = new ArrayList<>();

    getContract(signature, withProtocolInformation, requires, ensures, assignable);

    StringBuilder requiresBuilder = new StringBuilder();
    StringBuilder ensuresBuilder = new StringBuilder();
    StringBuilder assignableBuilder = new StringBuilder();

    for (String s : requires) {
      if (s.isBlank()) continue;
      if (!requiresBuilder.isEmpty()) requiresBuilder.append(" || ");
      requiresBuilder.append(s);
    }
    for (String s : ensures) {
      if (s.isBlank()) continue;
      if (!ensuresBuilder.isEmpty()) ensuresBuilder.append(" && ");
      ensuresBuilder.append(s);
    }
    for (String s : assignable) {
      if (s.isBlank()) continue;
      if (!assignableBuilder.isEmpty()) assignableBuilder.append(" ,");
      assignableBuilder.append(s);
    }

    String contract = "";
    if (!requiresBuilder.isEmpty()) {
      contract += "\n//@ requires " + requiresBuilder + ";";
    }
    if (!ensuresBuilder.isEmpty()) {
      contract += "\n//@ ensures " + ensuresBuilder + ";";
    }
    if (!assignableBuilder.isEmpty()) {
      contract += "\n//@ assignable " + assignableBuilder + ";";
    }

    return contract;
  }

  private void getContract(MethodSignature signature, boolean withProtocolInformation, List<String> requires, List<String> ensures, List<String> assignable) {
    MethodInformation info = contractLog.get(signature);
    if (info == null) return;
    if (withProtocolInformation) {
      requires.add(info.getRequiresWithProtocol());
      ensures.add(info.getEnsuresWithProtocol());
      assignable.add(info.getAssignableWithProtocol());
    } else {
      requires.add(info.getRequiresWithoutProtocol());
      ensures.add(info.getEnsuresWithoutProtocol());
      assignable.add(info.getAssignableWithoutProtocol());
    }
    for (String parent : info.parentTypes()) {
      getContract(new MethodSignature(parent, signature.methodName(), signature.parameterTypes()), withProtocolInformation, requires, ensures, assignable);
    }
  }

  /*
  protected void printTypestateAnnotationInformation(JCTree.JCMethodDecl tree, ClassUtils utils) {
    try {
      if (tree == null || tree.restype == null) return;
      Type treeType = tree.restype.type;
      if (treeType != null && utils.hasProtocol(treeType)) {
        List<State> statesList = utils.getGraph(treeType).getAllConcreteStates().stream().toList();

        for (JCTree.JCAnnotation annotation : tree.mods.annotations) {
          String type = annotation.annotationType.toString();
          if (type.equals("Ensures")) { //the @Ensures annotation is used for return types as well, instead of @State
            List<String> stateName = getValueOnly(annotation.args.head);
            long stateId = getStateIndex(stateName.get(0), statesList);
            if (stateId == -1) continue; //state doesn't exist
            printStateAnnotation(stateId, tree.getReturnType() + "");
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

  protected void printProtocolInformation(JCTree.JCMethodDecl tree, ClassUtils utils) {
    try {
      if (enclClassType == null || !utils.hasProtocol(enclClassType)) {
        return; //no protocol -> no information required
      }

      Graph graph = utils.getGraph(enclClassType);

      QuadMap<TreePrinterWithoutBodies.OriginalState, TreePrinterWithoutBodies.MethodName, TreePrinterWithoutBodies.ReturnedValue, TreePrinterWithoutBodies.NewState>
        quadMap = getAllMappings(graph);

      Name methodName = tree.name;
      String stateName = enclClassType + "State";
      if (methodName.toString().equals("<init>")) {
        printEnsuresComment(stateName + " == " + graph.getInitialState().getId());
      } else {
        Set<QuadMap.Entry<TreePrinterWithoutBodies.OriginalState, TreePrinterWithoutBodies.MethodName, TreePrinterWithoutBodies.ReturnedValue, TreePrinterWithoutBodies.NewState>>
          set = quadMap.getBMapping(new TreePrinterWithoutBodies.MethodName(methodName.toString()));
        if (set == null) return;
        List<String> originalStates = new ArrayList<>(set.size());
        for (QuadMap.Entry<TreePrinterWithoutBodies.OriginalState, TreePrinterWithoutBodies.MethodName, TreePrinterWithoutBodies.ReturnedValue, TreePrinterWithoutBodies.NewState> e : set) {
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
   */
  protected List<String> getValueOnly(JCTree tree) {
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

  protected void printStateAnnotation(long state, String paramClass) throws IOException {
    printEnsuresComment("\\result." + paramClass + "State == " + state);
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

  /**
   * This method creates a Map of all initial states and methods to the new state given the returned value.
   * If the transition between states is independent of the returned value, then the returned value is null.
   * @param graph the Graph containing the information about the transitions between states.
   * @return a QuadMap containing all transitions.
   */
  private QuadMap<OriginalState, MethodName, ReturnedValue, NewState> getAllMappings(Graph graph) {
    QuadMap<OriginalState, MethodName, ReturnedValue, NewState> quadMap = new QuadMap<>();

    Set<State> states = graph.getAllConcreteStates();

    BiMap<Long, State> statesMap = new BiMap<>();
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
          System.err.println("ERROR: " + value);
        }
      });
    }

    return quadMap;
  }

  protected record OriginalState (String originalStateId) {}
  //TODO: use method signature instead of name only
  protected record MethodName (String methodName) {}
  protected record ReturnedValue (String returnedValue) {}
  protected record NewState (String newStateId) {}

}
