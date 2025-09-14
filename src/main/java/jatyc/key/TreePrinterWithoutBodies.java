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
public class TreePrinterWithoutBodies extends CommonPrinterFeatures {
  private JavaTypestateChecker checker;
  private Type enclClassType;
  private String ghostVar;

  public TreePrinterWithoutBodies(Writer out, boolean sourceOutput, JavaTypestateChecker checker) {
    super(out, sourceOutput);
    this.checker = checker;
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
