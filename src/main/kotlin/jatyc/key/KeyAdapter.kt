package jatyc.key

import com.sun.source.tree.*
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit
import de.uka.ilkd.key.speclang.Contract
import jatyc.JavaTypestateChecker
import jatyc.key.contracts.ContractCreator
import jatyc.key.contracts.ContractLog
import jatyc.key.contracts.MethodSignature
import jatyc.key.treePrinter.TreePrinterForProofs
import jatyc.key.treePrinter.TreePrinterWithoutBodies
import jatyc.key.treeUtils.SignatureFinder
import jatyc.key.treeUtils.TreeCloner
import jatyc.key.treeUtils.TreeLogger
import java.io.StringWriter

/*TODO:
    Type x = y.foo(); -> typestate missmatch in protocol of y
    -
    y.foo(); -> typestate missmatch in protocol of y
    =>
    Type temp;
    temp = y.foo();
    Type x = temp;
    -
    Type temp;
    temp = y.foo();
    -
    use temp variables for KeY proofs
    -
    Alternative: track state within y
    -
    Translation of entire Project for KeY required
 */

/**
 * This class is used to allow for error checking using KeY.
 * When using KeY it is important that every file contains only one class.
 */
class KeyAdapter (val checker: JavaTypestateChecker) {
  val directory = TempDirectoryKey()
  private val sourceFiles = HashSet<String>()
  private val compilationUnits = HashMap<String, JCCompilationUnit>()
  private val jcTrees = HashMap<JCTree, String>()
  private val contractLog = ContractLog()
  private var converted = false
  private val convertedFiles = HashSet<String>()

  fun put(root: CompilationUnitTree) {
    val sourcePath = root.sourceFile.toString()
    if (sourceFiles.contains(sourcePath)) return
    sourceFiles.add(sourcePath)
    converted = false //new file needs conversion
    if (root is JCCompilationUnit) {
      root.accept(TreeLogger(jcTrees, sourcePath)) //saving a reference to the source-file for all JCTrees inside the JCCompilationUnit
      val clone = getClone(root)  //deep-cloning root to prevent information loss due to editing by the CFVisitor
      clone.accept(TreeCloner())
      compilationUnits[sourcePath] = clone
    }
  }

  private fun convert() {
    //TODO: figure out when the checker touches files the first time and when it actually checks them as the contracts might not include parent contracts if checked at the wrong time
    // Maybe the errors which are reported early are errors outside the java code? e.g. syntax errors
    for (root in compilationUnits.values) { //creating contract information of all files
      if (convertedFiles.contains(root.sourceFile.toString())) continue //file already converted
      root.accept(ContractCreator(contractLog, checker))
    }

    for (root in compilationUnits.values) { //creating files for KeY
      if (convertedFiles.contains(root.sourceFile.toString())) continue //file already converted
      convertedFiles.add(root.sourceFile.toString())

      val fileName = root.sourceFile.name.split("\\").last().split(".")

      val writer = StringWriter()
      val printer =
        TreePrinterWithoutBodies(writer, true, checker, contractLog)
      root.accept(printer)

      val content = writer.toString()

      print("\ncontent:\n$content")

      val packageName = if (root.packageName == null) {""} else {root.packageName.toString()}

      directory.putFile(fileName.first(), fileName.last(), content, packageName.split("."))
    }
    converted = true
  }

  fun check(source: Any) : Boolean {
    if (source !is JCTree) return false //sources should always be a JCTree, otherwise this adapter can't work with it.

    if (!converted) convert() //creating files for KeY whenever a file exists that isn't converted

    val result = performCheck(source)
    System.gc()

    println("RESULT: $result")

    return result
  }

  private fun performCheck(source: JCTree) : Boolean {
    val sourceFile = jcTrees[source] ?: return false //tree wasn't logged
    val root = compilationUnits[sourceFile] ?: return false //sourceFile wasn't logged (should be impossible given sourceFile != null)
    val methodSignature = methodSignatureFromError(source) ?: return false //should not, but might happen depending on the position of the error

    //converting file which needs testing
    val writer = StringWriter()
    val printer = TreePrinterForProofs(writer, true, this.checker, this.contractLog, methodSignature)
    root.accept(printer)

    val content = writer.toString()

    print("\ncontent:\n$content")

    //saving converted file
    val fileName = root.sourceFile.name.split("\\").last().split(".")
    val packageName = if (root.packageName == null) {""} else {root.packageName.toString()}

    directory.replaceFileForProof(fileName.first(), fileName.last(), content, packageName.split("."))

    //starting proof
    //val prover = KeyProver(file)
    val prover = KeyProver(directory.sourceDir)

    val contracts = prover.getContracts()
    var contractForProof : Contract? = null

    for (contract in contracts) {
      val contractSignature = methodSignatureFromKeyContract(contract) ?: continue
      if (methodSignature.equals(contractSignature.first) && contractSignature.first.classType.equals(contractSignature.second)) {
        contractForProof = contract
        break
      }
    }

    val result = prover.proveContract(contractForProof)

    if (contractForProof == null) {
      var paramTypes = ""
      for (paramType in methodSignature.parameterTypes) {
        if (paramTypes.isNotBlank()) paramTypes += ", "
        paramTypes += paramType
      }
      prover.log("Contract not found: ${methodSignature.classType}.${methodSignature.methodName}($paramTypes)")
    }

    //cleanup
    prover.dispose()
    directory.undoReplacements()

    return result
  }

  private fun getClone(original: JCCompilationUnit): JCCompilationUnit {
    val clone = original.clone()
    if (clone is JCCompilationUnit) {
      return clone
    }
    return original
  }

  private fun methodSignatureFromKeyContract(contract : Contract) : Pair<MethodSignature, String>? {
    val name = contract.name.split("[", "::", "(", ",", ")")

    //expected format: ClassName[ClassName2::MethodName(Parameter1, Parameter2, ... , ParameterN).JML...]

    if (name.size < 5) {
      return null //the given String doesn't match the expected format
    }

    //position 0: class, which contains method
    //position 1: class, which defines method (and a contract)
    //position 2: method name
    //position 3 to last - 1: parameter types
    //last position: irrelevant information about the contract

    val parameterTypes = name.subList(3, name.size - 1).filter { it.isNotBlank() }

    return Pair(MethodSignature(name[0], name[2], parameterTypes), name[1])
  }

  private fun methodSignatureFromError(source: JCTree) : MethodSignature?{
    val fileName = jcTrees[source]

    val signatureFinder = SignatureFinder(source)

    compilationUnits[fileName]?.accept(signatureFinder)

    return signatureFinder.getMethodSignatur()
  }
}
