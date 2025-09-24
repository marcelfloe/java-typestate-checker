package jatyc.key.contracts;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.util.Name;
import jatyc.JavaTypestateChecker;
import jatyc.core.JavaType;
import jatyc.typestate.graph.DecisionState;
import jatyc.typestate.graph.Graph;
import jatyc.typestate.graph.State;
import jatyc.util.multimap.BiMap;
import jatyc.util.multimap.QuadMap;
import jatyc.utils.ClassUtils;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.jetbrains.annotations.NotNull;

// TODO: add JML for missing Annotations (no requires -> all states possible; no ensures -> end (or droppable?; end is enough as var can't be used anymore, but assertions need to check for end and droppable); no state -> unknown/all states possible)

/**
 * This class creates the contracts of the methods without including the parent contracts, but a reference to the parent types.
 */
public class ContractCreator extends Pretty {
  private final ContractLog contractLog;
  private final JavaTypestateChecker checker;
  private Type enclClassType;

  public ContractCreator(ContractLog contractLog, JavaTypestateChecker checker) {
    super(new Writer() { //this writer isn't supposed to write anything; pretty is only used to properly visit the entire given tree
      @Override
      public void write(@NotNull char[] cbuf, int off, int len) {}

      @Override
      public void flush() {}

      @Override
      public void close() {}
    }, true);
    this.contractLog = contractLog;
    this.checker = checker;
  }

  @Override
  public void visitClassDef(JCTree.JCClassDecl tree) {
    Type prevClassType = enclClassType;
    enclClassType = tree.type;
    super.visitClassDef(tree);
    enclClassType = prevClassType;
  }

  @Override
  public void visitMethodDef(JCTree.JCMethodDecl tree) {
    createAndLogContract(tree);
    super.visitMethodDef(tree);
  }

  private void createAndLogContract(JCTree.JCMethodDecl tree) {
    if (enclClassType == null) return;
    String classType = checker.getUtils().typeIntroducer.getJavaType(enclClassType) + "";

    List<String> requiresAnnotations = new ArrayList<>();
    List<String> ensuresAnnotations = new ArrayList<>();
    List<String> assignableAnnotations = new ArrayList<>();
    getAnnotationInformation(requiresAnnotations, ensuresAnnotations, assignableAnnotations, tree);

    List<String> requiresProtocol = new ArrayList<>();
    List<String> ensuresProtocol = new ArrayList<>();
    List<String> assignableProtocol = new ArrayList<>();
    getProtocolInformation(requiresProtocol, ensuresProtocol, assignableProtocol, tree);

    ContractInformation annotationInformation = new ContractInformation(requiresAnnotations, ensuresAnnotations, assignableAnnotations);
    ContractInformation protocolInformation = new ContractInformation(requiresProtocol, ensuresProtocol, assignableProtocol);

    List<String> superTypes = getSuperTypes(enclClassType);

    MethodSignature signature = createMethodSignature(tree, classType);
    MethodInformation methodInformation = new MethodInformation(signature, annotationInformation, protocolInformation, superTypes);

    contractLog.log(methodInformation);
  }

  private List<String> getSuperTypes(Type type) {
    if (type == null) return new ArrayList<>();
    JavaType javaType = checker.getUtils().typeIntroducer.getJavaType(type);
    return getSuperTypesRecursive(javaType).stream().map(
      JavaType::qualifiedName).toList();
  }

  private Set<JavaType> getSuperTypesRecursive(JavaType type) {
    Set<JavaType> supertypes = new HashSet<>();
    if (type == null) return supertypes;
    for (JavaType supertype : type.getSuperTypes()) {
      supertypes.add(supertype);
      supertypes.addAll(getSuperTypesRecursive(supertype));
    }
    return supertypes;
  }

  private void getAnnotationInformation(List<String> requires, List<String> ensures, List<String> assignable, JCTree.JCMethodDecl tree) {
    if (tree == null || tree.restype == null) return;
    Type treeType = tree.restype.type;
    ClassUtils utils = checker.getUtils().classUtils;
    if (treeType != null && utils.hasProtocol(treeType)) {
      boolean stateAnnotationExists = false;
      List<State> statesList = utils.getGraph(treeType).getAllConcreteStates().stream().toList();//getting "@State"-Annotation (actually using "@Ensures" but at a different position to parameters)
      for (JCTree.JCAnnotation annotation : tree.mods.annotations) {
        String type = annotation.annotationType.toString();
        if (type.equals("Ensures")) { //the @Ensures annotation is used for return types as well, instead of @State
          List<String> stateName = getValueOnly(annotation.args.head);
          long stateId = getStateIndex(stateName.get(0), statesList);
          if (stateId == -1) continue; //state doesn't exist
          ensures.add("\\result." + tree.getReturnType() + "State == " + stateId);
          stateAnnotationExists = true;
          break;
        }
      }
      if (!stateAnnotationExists) {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        for (State state : statesList) {
          if (!sb.isEmpty()) sb.append(" || ");
          sb.append("\\result." + tree.getReturnType() + "State == " + state.getId());
        }
        sb.append(")");
        ensures.add(sb.toString());
      }
    }

    for (JCTree.JCVariableDecl varDecl : tree.params) { //getting @Ensures and @Requires of the parameters
      if (varDecl.type == null) {
        continue;
      }
      boolean protocolExists = utils.hasProtocol(varDecl.type);
      boolean ensuresAnnotationExists = false;
      boolean requiresAnnotationExists = false;
      if (protocolExists) {
        List<State> statesList = utils.getGraph(varDecl.type).getAllConcreteStates().stream().toList();
        for (JCTree.JCAnnotation annotation : varDecl.mods.annotations) {
          String type = annotation.annotationType.toString();
          String paramName = getParamName(varDecl);
          String paramClass = getParamClass(varDecl);
          if (type.equals("Ensures")) {
            List<String> stateName = getValueOnly(annotation.args.head);
            long stateId = getStateIndex(stateName.get(0), statesList);
            if (stateId == -1) continue; //state doesn't exist
            ensures.add(paramName + "." + paramClass + "State == " + stateId);
            ensuresAnnotationExists = true;
          } else if (type.equals("Requires")) {
            List<String> stateName = getValueOnly(annotation.args.head);
            List<Long> stateIds = new ArrayList<>(stateName.size());
            for (String s : stateName) {
              long stateId = getStateIndex(s, statesList);
              if (stateId == -1) continue; //state doesn't exist
              stateIds.add(stateId);
            }
            requiresAnnotationExists = true;
            requires.add(getOr(stateIds.stream().map(stateId -> paramName + "." + paramClass + "State == " + stateId).toList()));
          }

          if (!ensuresAnnotationExists) {
            long stateId = getStateIndex("end", statesList);
            if (stateId != -1) ensures.add(paramName + "." + paramClass + "State == " + stateId);
          }
          if (!requiresAnnotationExists) {
            requires.add(getOr(statesList.stream().map(state -> paramName + "." + paramClass + "State == " + state.getId()).toList()));
          }
          assignable.add(paramName + "." + paramClass + "State");
        }
      }
    }
  }

  private void getProtocolInformation(List<String> requires, List<String> ensures, List<String> assignable, JCTree.JCMethodDecl tree) {
    ClassUtils utils = checker.getUtils().classUtils;
    if (enclClassType == null || !utils.hasProtocol(enclClassType)) {
      return; //no protocol -> no information required
    }
    Graph graph = utils.getGraph(enclClassType);
    QuadMap<OriginalState, MethodSignature, ReturnedValue, NewState>
      quadMap = getAllMappings(graph);
    Name methodName = tree.name;
    String stateName = enclClassType + "State";
    if (methodName.toString().equals("<init>")) {
      //TODO: This might not apply to different constructors
      // Are other constructors properly managed by the normal method handling?
      ensures.add(stateName + " == " + graph.getInitialState().getId());
    } else {
      Set<QuadMap.Entry<OriginalState, MethodSignature, ReturnedValue, NewState>>
        set = quadMap.getBMapping(createMethodSignature(tree, enclClassType + ""));
      if (set == null) return;
      List<String> originalStates = new ArrayList<>(set.size());
      for (QuadMap.Entry<OriginalState, MethodSignature, ReturnedValue, NewState> e : set) {
        originalStates.add(e.w().originalStateId);
        if (e.y() == null) {
          ensures.add("\\old(" + stateName + ") == " + e.w().originalStateId + " ==> " + stateName + " == " + e.z().newStateId);
        } else {
          ensures.add("(\\old(" + stateName + ") == " + e.w().originalStateId + " && \\result == " + e.y().returnedValue +") ==> " + stateName + " == " + e.z().newStateId);
        }
      }
      requires.add(getOr(originalStates.stream().distinct().map(s -> stateName + " == " + s).toList()));
    }
    assignable.add(stateName);
  }

  private List<String> getValueOnly(JCTree tree) {
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

  private String getOr(List<String> list) {
    StringBuilder sb = new StringBuilder();
    if (list.isEmpty()) return sb.toString();
    sb.append(list.get(0));
    for (int i = 1; i < list.size(); i++) {
      sb.append(" || ").append(list.get(i));
    }
    return sb.toString();
  }

  /**
   * This method creates a Map of all initial states and methods to the new state given the returned value.
   * If the transition between states is independent of the returned value, then the returned value is null.
   * @param graph the Graph containing the information about the transitions between states.
   * @return a QuadMap containing all transitions.
   */
  private QuadMap<OriginalState, MethodSignature, ReturnedValue, NewState> getAllMappings(Graph graph) {
    QuadMap<OriginalState, MethodSignature, ReturnedValue, NewState> quadMap = new QuadMap<>();

    Set<State> states = graph.getAllConcreteStates();

    BiMap<Long, State> statesMap = new BiMap<>();
    states.forEach(state -> statesMap.map(state.getId(), state));

    for (State state : states) {
      OriginalState
        originalState = new OriginalState(state.getId() + "");

      state.getTransitions().forEach((key, value) -> {
        String returnType = key.getReturnType().stringName();
        String methodName = key.getName();
        List<String> methodParameters = key.getArgs().stream().map(arg -> arg + "").toList();
        MethodSignature methodSignature = new MethodSignature(enclClassType + "", methodName, methodParameters);
        if (value instanceof DecisionState) {
          ((DecisionState) value).getTransitions().forEach((k,v) -> {
            if (returnType.equals("boolean")) { //-> boolean
              quadMap.map(originalState, methodSignature, new ReturnedValue(k.getLabel()), new NewState(v.getId() + ""));
            } else { //-> enum
              quadMap.map(originalState, methodSignature, new ReturnedValue(returnType + "." + k.getLabel()), new NewState(v.getId() + ""));
            }
          });
        } else if (value instanceof State) {
          quadMap.map(originalState, methodSignature, null, new NewState(((State) value).getId() + ""));
        } else {
          System.out.println("ERROR: " + value);
        }
      });
    }

    return quadMap;
  }

  protected record OriginalState (String originalStateId) {}
  protected record ReturnedValue (String returnedValue) {}
  protected record NewState (String newStateId) {}

  public static MethodSignature createMethodSignature(JCTree.JCMethodDecl tree, String enclosingClass) {
    return new MethodSignature(enclosingClass, tree.name + "", new ArrayList<>(tree.params.map(p -> {if (p.type == null) {return "";} else {return p.type.baseType() + "";}})));
  }
}
