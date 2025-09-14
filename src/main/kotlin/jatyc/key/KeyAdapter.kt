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


class KeyAdapter (val checker: JavaTypestateChecker) {
  val prover = KeyProver()
  val directory = TempDirectoryKey()
  private val sourceFiles = HashSet<String>()
  private val compilationUnits = HashMap<String, CompilationUnitTree>()

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
    println(sourcePath)
    sourceFiles.add(sourcePath)
    compilationUnits[sourcePath] = root

    val fileName = root.sourceFile.name.split("\\").last().split(".")

    val content : String = if (root is JCTree) {
      val writer = StringWriter()
      val printer = TreePrinterWithoutBodies(writer, true, checker)
      root.accept(printer)
      writer.toString()
    } else {""}

    val packageName = if (root.packageName == null) {""} else {root.packageName.toString()}

    directory.putFile(fileName.first(), fileName.last(), content, packageName.split("."))
  }
}
