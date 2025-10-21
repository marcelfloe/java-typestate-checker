package jatyc.key;

import java.io.File;
import java.util.*;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableSet;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

//TODO: find memory leak
// (might be a leak in JaTyC only triggered by the big instances of KeY)

/**
 * Class which proves all proof obligations of the source file, which are provided to proveContract(), using KeY.
 * Based on <a href="https://github.com/KeYProject/key/blob/nightly/key.core.example/src/main/java/org/key_project/Main.java">https://github.com/KeYProject/key/blob/nightly/key.core.example/src/main/java/org/key_project/Main.java</a>
 */
public class KeyProver {

  private int maxSteps_ = 10000;
  private final Logger LOGGER = LoggerFactory.getLogger(KeyProver.class);
  private KeYEnvironment<?> env;

  /**
   * Creates a new KeyProver for proving contracts in the given file.
   * @param file the file/directory containing the code which needs proving
   */
  public KeyProver(File file) {
    if (file == null) return;
    LOGGER.info("Starting KeY example application.");
    maxSteps_ = 10000;
    try {
      // Ensure that Taclets are parsed
      this.env = setupEnvironment(file);
    } catch (ProblemLoaderException e) {
      LOGGER.info("Exception at '{}'", file, e);
    }
  }

  /**
   * Sets up the environment with the Java file
   *
   * @param file the File with the Java source code to be verified.
   * @return the {@KeYEnvironment} that provides the context for all following verification tasks.
   * @throws ProblemLoaderException if the setup fails
   */
  private KeYEnvironment<?> setupEnvironment(File file) throws ProblemLoaderException {
    List<File> classPaths = null; // Optionally: Additional specifications for API classes
    File bootClassPath = null; // Optionally: Different default specifications for Java API
    List<File> includes = null; // Optionally: Additional includes to consider

    if (!ProofSettings.isChoiceSettingInitialised()) {
      KeYEnvironment<?> env =
        KeYEnvironment.load(file, classPaths, bootClassPath, includes);
      env.dispose();
    }

    // Set Taclet options
    ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
    Map<String, String> oldSettings = choiceSettings.getDefaultChoices();
    Map<String, String> newSettings = new HashMap<>(oldSettings);
    newSettings.putAll(MiscTools.getDefaultTacletOptions());
    choiceSettings.setDefaultChoices(newSettings);
    // Load source code
    return KeYEnvironment.load(file, classPaths, bootClassPath, includes);
  }

  /**
   * Collect all contracts (proof obligations) for the given environment.
   *
   * @return list of {@link Contract}s to be proven
   */
  public List<Contract> getContracts() {
    if (env == null) return new ArrayList<>();
    // List all specifications of all types in the source location (not classPaths and
    // bootClassPath)
    final List<Contract> proofContracts = new LinkedList<>();
    Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
    for (KeYJavaType type : kjts) {
      if (!KeYTypeUtil.isLibraryClass(type)) {
        ImmutableSet<IObserverFunction> targets =
          env.getSpecificationRepository().getContractTargets(type);
        for (IObserverFunction target : targets) {
          ImmutableSet<Contract> contracts =
            env.getSpecificationRepository().getContracts(type, target);
          for (Contract contract : contracts) {
            proofContracts.add(contract);
          }
        }
      }
    }
    return proofContracts;
  }

  /**
   * Triggers the start of a proof by KeY.
   * @param contract the contract which gets proven.
   * @return whether the proof was successful or not.
   */
  public boolean proveContract(Contract contract) {
    if (this.env == null || contract == null) return false;
    return proveContract(this.env, contract);
  }

  /**
   * Triggers the start of a proof by KeY.
   * @param contract the contract which gets proven.
   * @param maxSteps_ the maximum amount of steps KeY is allowed to use.
   * @return whether the proof was successful or not.
   */
  public boolean proveContract(Contract contract, int maxSteps_) {
    int temp = this.maxSteps_;
    this.maxSteps_ = maxSteps_;
    boolean result = proveContract(contract);
    this.maxSteps_ = temp;
    return result;
  }

  /**
   * tries to prove the given contract in the specified environment
   *
   * @param env the {@link KeYEnvironment} in which to prove the contract
   * @param contract the {@link Contract} to be proven
   */
  private boolean proveContract(KeYEnvironment<?> env, Contract contract) {
    Proof proof = null;
    boolean closed = false;
    try {
      // Create proof
      proof =
        env.createProof(contract.createProofObl(env.getInitConfig(), contract));
      // Set proof strategy options
      StrategyProperties sp =
        proof.getSettings().getStrategySettings().getActiveStrategyProperties();
      sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
        StrategyProperties.METHOD_CONTRACT);
      sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
        StrategyProperties.DEP_ON);
      sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
        StrategyProperties.QUERY_ON);
      sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
        StrategyProperties.NON_LIN_ARITH_DEF_OPS);
      sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY,
        StrategyProperties.STOPMODE_NONCLOSE);
      proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
      // Make sure that the new options are used
      int maxSteps = maxSteps_;
      ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
      ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
        .setActiveStrategyProperties(sp);
      proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
      proof.setActiveStrategy(proof.getServices().getProfile()
        .getDefaultStrategyFactory().create(proof, sp));
      // Start auto mode
      env.getUi().getProofControl().startAndWaitForAutoMode(proof);
      // Show proof result
      closed = proof.openGoals().isEmpty();
      LOGGER.info("Contract '" + contract.getDisplayName() + "' of "
        + contract.getTarget() + " is " + (closed ? "verified" : "still open")
        + ".");
    } catch (ProofInputException e) {
      LOGGER.error("Exception at {} of {}", contract.getDisplayName(),
        contract.getTarget());
    } finally {
      if (proof != null) {
        proof.dispose(); // Ensure always that all instances of Proof are
        // disposed
      }
    }
    return closed; //if proof is closed then the proof was successful
  }

  /**
   * Logs the given message.
   * @param message the message which is supposed to be logged.
   */
  public void log(String message) {
    LOGGER.info(message);
  }

  /**
   * Disposes of the environment.
   */
  public void dispose() {
    if (env != null) env.dispose();
  }
}
