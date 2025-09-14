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

/**
 * Class which proves all proof obligations of the source file using KeY.
 * Based on https://github.com/KeYProject/key/blob/nightly/key.core.example/src/main/java/org/key_project/Main.java
 */
public class KeyProver {

  private static int maxSteps_;
  private static final Logger LOGGER = LoggerFactory.getLogger(KeyProver.class);

  /**
   * The entry point of the prover.
   *
   * @param file The file which is supposed to be proved.
   * @return true if the proof was successful, false if not
   */
  public static boolean proofFile(File file) {
    System.out.println("LENGTH: " + file.length());
    LOGGER.info("Starting KeY example application.");
    maxSteps_ = 10000;
    KeYEnvironment<?> env = null;
    try {
      // Ensure that Taclets are parsed
      env = setupEnvironment(file);
      return proveEnvironmemt(env);
    } catch (ProblemLoaderException e) {
      LOGGER.info("Exception at '{}'", file, e);
      System.out.println("EXEPTION IN PROBLEM LOADER: " + e.getMessage());
      //proofing wasn't successful
      return false;
    } finally {
      if (env != null) {
        env.dispose();
      }
      System.out.println("DISPOSED");
    }
  }

  /**
   * The entry point of the prover.
   *
   * @param file The file which is supposed to be proved.
   * @param maxSteps The maximum amount of steps the prover uses.
   * @return true if the proof was successful, false if not
   */
  public static boolean proofFile(File file, int maxSteps) {
    maxSteps_ = maxSteps;
    try {
      // Ensure that Taclets are parsed
      KeYEnvironment<?> env = setupEnvironment(file);
      return proveEnvironmemt(env);
    } catch (ProblemLoaderException e) {
    }
    return false;
  }


  /**
   * Sets up the environment with the Java file
   *
   * @param file the File with the Java source code to be verified.
   * @return the {@KeYEnvironment} that provides the context for all following verification tasks.
   * @throws ProblemLoaderException if the setup fails
   */
  private static KeYEnvironment<?> setupEnvironment(File file) throws ProblemLoaderException {
    List<File> classPaths = null; // Optionally: Additional specifications for API classes
    File bootClassPath = null; // Optionally: Different default specifications for Java API
    List<File> includes = null; // Optionally: Additional includes to consider

    System.out.println("ProofSettings upcoming");
    if (!ProofSettings.isChoiceSettingInitialised()) {
      System.out.println("ProofSettings choice setting not yet initialized");
      KeYEnvironment<?> env =
        KeYEnvironment.load(file, classPaths, bootClassPath, includes);
      env.dispose();
    }
    System.out.println("ProofSettings choice setting initialized");

    // Set Taclet options
    ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
    Map<String, String> oldSettings = choiceSettings.getDefaultChoices();
    Map<String, String> newSettings = new HashMap<>(oldSettings);
    newSettings.putAll(MiscTools.getDefaultTacletOptions());
    choiceSettings.setDefaultChoices(newSettings);
    // Load source code
    KeYEnvironment<?> env =
      KeYEnvironment.load(file, classPaths, bootClassPath, includes);
    return env;
  }

  /**
   * Proves every specification for which KeY knows how to generate a contract.
   *
   * @param env the {@link KeYEnvironment} to be verified
   */
  private static boolean proveEnvironmemt(KeYEnvironment<?> env) {
    final List<Contract> proofContracts = getContracts(env);
    //System.out.println("Found contracts:" + proofContracts.size());
    try {
      for (Contract contract : proofContracts) {
        LOGGER.info("Found contract '" + contract.getDisplayName());
        if (!proveContract(env, contract)) return false; //contract can't be proved
      }
    } finally {
      env.dispose(); // Ensure always that all instances of KeYEnvironment are disposed
    }

    return true; //all contracts have been proven
  }

  /**
   * Collect all contracts (proof obligations) for the given environment.
   *
   * @param env the {@link KeYEnvironment} to look for contracts
   * @return list of {@link Contract}s to be proven
   */
  private static List<Contract> getContracts(KeYEnvironment<?> env) {
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
   * tries to prove the given contract in the specified environment
   *
   * @param env the {@link KeYEnvironment} in which to prove the contract
   * @param contract the {@link Contract} to be proven
   */
  private static boolean proveContract(KeYEnvironment<?> env, Contract contract) {
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
      if (!closed) {
        System.out.println(proof.openGoals());
      }
    } catch (ProofInputException e) {
      LOGGER.error("Exception at {} of {}", contract.getDisplayName(),
        contract.getTarget());
      System.out.println("EXCEPTION WITH PROOF INPUT: " + e.getMessage());
        contract.getTarget();
    } finally {
      if (proof != null) {
        proof.dispose(); // Ensure always that all instances of Proof are
        // disposed
      }
    }
    return closed; //if proof is closed then the proof was successful
  }
}
