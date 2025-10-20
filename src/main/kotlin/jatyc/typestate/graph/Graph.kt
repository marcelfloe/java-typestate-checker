package jatyc.typestate.graph

import com.sun.tools.javac.comp.AttrContext
import com.sun.tools.javac.comp.Env
import jatyc.typestate.*
import jatyc.utils.JTCUtils
import java.nio.file.Path

class Graph constructor(val resolvedFile: Path, val typestateName: String) {
  val userPath = JTCUtils.getUserPath(resolvedFile)
  val filename = resolvedFile.fileName
  private var env: Env<AttrContext>? = null
  private var initialState: State? = null
  private val endState = EndState()
  private val unknownState = UnknownState() // A state that is superstate of all states
  private val namedStates = HashMap<String, State>()
  private val referencedStates = HashSet<String>()
  private val concreteStates = mutableSetOf<State>()
  var unusedStates: List<TStateNode>? = null

  init {
    namedStates[END_STATE_NAME] = endState
  }

  fun getEnv() = env!!
  fun setEnv(env: Env<AttrContext>) {
    this.env = env
  }
  fun getInitialState() = initialState!!
  fun getUnknownState() = unknownState
  fun getAllConcreteStates(): Set<State> = concreteStates
  fun getAllTransitions(): Sequence<MethodTransition> = sequence {
    for (state in concreteStates) {
      for (method in state.normalizedTransitions) {
        yield(method.key)
      }
    }
  }

  fun hasStateByName(name: String): Boolean {
    return namedStates[name] != null
  }

  private fun getStateByName(id: TIdNode): State {
    return namedStates[id.name] ?: throw StateNotDefined(id)
  }

  private fun getStateByNode(node: TStateNode): State {
    return if (node.name == null) {
      State(node)
    } else namedStates[node.name]!!
    // namedStates is initialized by the time this is called
  }

  private fun getStateByNode(node: TDecisionStateNode): DecisionState {
    return DecisionState(node)
  }

  private fun traverseState(node: TStateNode): State {
    val state = getStateByNode(node)
    if (node.name == null || referencedStates.add(node.name)) {
      concreteStates.add(state)
      for (method in node.methods) {
        state.addTransition(method, traverseDestination(method.destination))
      }
    }
    return state
  }

  private fun traverseDecision(node: TDecisionStateNode): DecisionState {
    val state = getStateByNode(node)
    for (decision in node.decisions) {
      state.addTransition(decision, traverseDestination(decision.destination) as State)
    }
    return state
  }

  private fun traverseDestination(node: TNode): AbstractState<*> {
    if (node is TIdNode) {
      return if (node.name == END_STATE_NAME) {
        concreteStates.add(endState)
        endState
      } else traverseState(getStateByName(node).node!!)
    }
    if (node is TStateNode) return traverseState(node)
    if (node is TDecisionStateNode) return traverseDecision(node)
    throw AssertionError("wrong destination $node")
  }

  private fun addNamedState(node: TStateNode) {
    if (node.name == null) {
      throw AssertionError("state without name?")
    }
    if (RESERVED_STATE_NAMES.contains(node.name)) {
      throw ReservedStateName(node)
    }
    namedStates.compute(node.name) { _: String?, old: State? ->
      if (old == null) State(node) else throw DuplicateState(old.node!!, node)
    }
  }

  fun traverseTypestate(node: TDeclarationNode) {
    for (state in node.states) {
      addNamedState(state)
    }
    initialState = traverseState(node.states[0])
    // Calculate if there are any unused states
    val unusedStates: MutableSet<String> = HashSet(namedStates.keys)
    unusedStates.removeAll(referencedStates)
    if (unusedStates.size > 0) {
      this.unusedStates = unusedStates.mapNotNull { namedStates[it]!!.node }
    }
  }

  companion object {
    const val END_STATE_NAME = "end"
    val RESERVED_STATE_NAMES: List<String> = listOf(END_STATE_NAME)
  }
}
