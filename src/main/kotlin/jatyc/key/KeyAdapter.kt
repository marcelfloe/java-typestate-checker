package jatyc.key

import com.sun.source.tree.*
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit
import jatyc.JavaTypestateChecker
import jatyc.key.contracts.ContractCreator
import jatyc.key.contracts.ContractLog
import jatyc.key.treePrinter.TreePrinterForProofs
import jatyc.key.treePrinter.TreePrinterWithoutBodies
import jatyc.key.treeUtils.TreeCloner
import jatyc.key.treeUtils.TreeLogger
import java.io.StringWriter
import java.nio.file.Path
import kotlin.io.path.extension

//TODO: provide method to start a proof for one method

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


/*
TODO:
 -transform code to include JML (including JML based on protocols) and save files
 -whenever the typestate checker finds a problem:
  - transform the class which includes the problem and replace the previous transformed file (save old file in different directory; new file does not include state information in contract of problematic method)
  - then use KeY to prove the state at the problematic position
  - then replace the file with the old file again
 */


/**
 * This class is used to allow for error checking using KeY.
 * When using KeY it is important that every file contains only one class.
 */
class KeyAdapter (val checker: JavaTypestateChecker) {
  val prover = KeyProver()
  val directory = TempDirectoryKey()
  private val sourceFiles = HashSet<String>()
  private val compilationUnits = HashMap<String, JCCompilationUnit>()
  private val jcTrees = HashMap<JCTree, String>()
  private val contractLog = ContractLog()
  private var converted = false

  fun test(test: CompilationUnitTree) {

    /*
    println("starting KeY with classfile: " + test.static.name)
    //creating temp file to give to KeY
    //the new directory is required as KeY always tries to load the entire directory of the source file
    val directory =  Files.createTempDirectory("jatyc-key").toFile()
    val file = File.createTempFile("tmp",".java", directory)
    //val fileWriter = FileWriter(file)
    //converting source code to code KeY can use
    file.appendText(createFileContent(test.cfRoot))
    println("total space: " + file.totalSpace + "; free space: " + file.freeSpace)
    //proving the code using KeY
    val isProofSuccessful = KeyProver.proofFile(file)
    println(isProofSuccessful)
    //file cleanup
    file.delete()
    directory.delete()
     */
  }

  fun put(root: CompilationUnitTree) {
    val sourcePath = root.sourceFile.toString()
    if (sourceFiles.contains(sourcePath)) return
    sourceFiles.add(sourcePath)
    if (root is JCCompilationUnit) {
      root.accept(TreeLogger(jcTrees, sourcePath)) //saving a reference to the source-file for all JCTrees inside the JCCompilationUnit
      val clone = getClone(root)  //deep-cloning root to prevent information loss due to editing by the CFVisitor
      clone.accept(TreeCloner())
      compilationUnits[sourcePath] = clone
    }
  }

  fun convert() {
    for (root in compilationUnits.values) { //creating all contracts for all given classes and their methods
      if (root is JCTree) root.accept(ContractCreator(contractLog, checker))
    }

    for (root in compilationUnits.values) { //creating files for KeY

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
  }

  fun check(source: Any, messageKey: String, vararg args: Any?) : Boolean {
    if (source !is JCTree) return false //sources should always be a JCTree, otherwise this adapter can't work with it.


    if (!converted) { //creating files for KeY on first call
      convert()
      converted = true
    }

    println("Source is JCTree: $source")
    val sourceFile = jcTrees[source]
    println("Source-file of source: $sourceFile")
    println(compilationUnits[sourceFile]?.sourceFile)
    println("MessageKey: $messageKey")
    val root = compilationUnits[sourceFile] ?: return false //sourcefile wasn't logged

    val writer = StringWriter()
    val printer = TreePrinterForProofs(writer, true, this.checker, this.contractLog, source, messageKey, args)
    root.accept(printer)

    println(writer.toString())

    val content = writer.toString()

    print("\ncontent:\n$content")

    val fileName = root.sourceFile.name.split("\\").last().split(".")

    val packageName = if (root.packageName == null) {""} else {root.packageName.toString()}

    directory.replaceFileForProof(fileName.first(), fileName.last(), content, packageName.split("."))

    directory.undoReplacements()

    /*
    println("---Source---")
    println(source)
    println("pos(): " + source.pos())
    println("pos: " + source.pos)
    println("tag: " + source.tag)
    println("type: " + source.type)
    println("kind: " + source.kind)
    println("javaClass: " + source.javaClass)
    println("preferredPosition: " + source.preferredPosition)
    println("startPosition: " + source.startPosition)
    println("---MessageKey---")
    println(messageKey)
    println("---Args---")
    args.iterator().forEach {
      if (it != null) {
        println(it.javaClass)
      }
    }
    println("++++++++++")
     */

    //TODO: identify method which needs checking
    //TODO: replace file with new method contract
    //TODO: identify contract which needs proving
    //TODO: prove contract
    //TODO: undo file replacement
    //TODO: report about contract proving success

    //TODO: implement error checking
    return false
  }

  //TODO: this method seems to be called only for .protocol-files
  // So the method should be irrelevant, as KeY can only check .java-files
  fun check(message: String, file: Path, pos: Int) : Boolean {
    if (!file.extension.equals("java")) return false //KeY can only check Java Code in java files

    if (!converted) { //creating files for KeY on first call
      convert()
      converted = true
    }

    //TODO: identify method which needs checking
    //TODO: replace file with new method contract
    //TODO: identify contract which needs proving
    //TODO: prove contract
    //TODO: undo file replacement
    //TODO: report about contract proving success

    //TODO: implement error checking
    return false
  }

  private fun getClone(original: JCCompilationUnit): JCCompilationUnit {
    val clone = original.clone()
    if (clone is JCCompilationUnit) {
      return clone
    }
    return original
  }
}
