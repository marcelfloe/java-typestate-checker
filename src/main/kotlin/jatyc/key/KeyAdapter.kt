package jatyc.key

import com.sun.source.tree.*
import com.sun.tools.javac.tree.JCTree
import jatyc.JavaTypestateChecker
import java.io.StringWriter

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
  private val compilationUnits = HashMap<String, CompilationUnitTree>()
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
    compilationUnits[sourcePath] = root
  }

  fun convert() {
    for (root in compilationUnits.values) { //creating all contracts for all given classes and their methods
      if (root is JCTree) root.accept(ContractCreator(contractLog, checker))
    }

    for (root in compilationUnits.values) { //creating files for KeY

      val fileName = root.sourceFile.name.split("\\").last().split(".")

      val content : String = if (root is JCTree) {
        val writer = StringWriter()
        val printer = TreePrinterWithoutBodies(writer, true, checker, contractLog)
        root.accept(printer)
        writer.toString()
      } else {""}

      print("\ncontent:\n$content")

      val packageName = if (root.packageName == null) {""} else {root.packageName.toString()}

      directory.putFile(fileName.first(), fileName.last(), content, packageName.split("."))

    }
  }

  fun check() {
    if (!converted) {
      convert()
      converted = true
    }
    //TODO: implement error checking
  }
}
