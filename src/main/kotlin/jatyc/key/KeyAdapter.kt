package jatyc.key

import com.sun.source.tree.CompilationUnitTree
import jatyc.core.cfg.ClassDeclAndCompanion
import java.io.File
import java.nio.file.Files

//nonStatic.graph contains states and their transitions

class KeyAdapter {
  companion object {

    val testCode = """
      public class IntegerUtil {
         /*@ normal_behavior
           @ ensures \result == x + y;
           @*/
         public static int add(int x, int y) {
            return x + y;
         }

         /*@ normal_behavior
           @ ensures \result == x - y;
           @*/
         public static int sub(int x, int y) {
            return x - y;
         }
      }
    """.trimIndent()

    fun test(test: ClassDeclAndCompanion) {
      /*
      println("""
        -------------------------
        Test:
          ${test.static.name}
          xxxxxxxxxxxxxxxxxxxx
          ${test.nonStatic.name}
          xxxxxxxxxxxxxxxxxxxx
          ${test.cfRoot.toString()}
          xxxxxxxxxxxxxxxxxxxx
          ${test.cfTree.toString()}
          xxxxxxxxxxxxxxxxxxxx
          ${test.cfTree?.kind?.name}
          xxxxxxxxxxxxxxxxxxxx
          ${test.cfType.toString()}
          xxxxxxxxxxxxxxxxxxxx
          ${test.cfType?.kind?.name}
        -------------------------
      """.trimIndent())
       */
      /*
      val ast = test.cfRoot
      println("""

        XXXXXXXXXXXXXXXXXXXXXXXXXXX
        ${ast?.`package`.toString()}
        XXXXXXXXXXXXXXXXXXXXXXXXXXX
        ${ast?.imports.toString()}
        XXXXXXXXXXXXXXXXXXXXXXXXXXX
        ${ast?.kind?.name}
        XXXXXXXXXXXXXXXXXXXXXXXXXXX
        ${ast?.sourceFile.toString()}
        XXXXXXXXXXXXXXXXXXXXXXXXXXX
        ${ast?.packageName.toString()}
        XXXXXXXXXXXXXXXXXXXXXXXXXXX

      """.trimIndent())
       */
      //println(test.nonStatic.cfRoot.toString().equals(test.static.cfRoot.toString()))
      /*
      println(test.nonStatic.graph == null)
      println(test.nonStatic.graph)
      println(test.static.graph == null)
      println(test.static.graph)
      val graph = test.nonStatic.graph
      println("XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX")
      if (graph != null) {
        graph.getAllConcreteStates().forEach {
          println(it)
          println(it.transitions)
        }
      }
      println("XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX")
       */

      //creating temp file to give to KeY
      //the new directory is required as KeY always tries to load the entire directory of the source file
      val directory =  Files.createTempDirectory("jatyc-key").toFile()
      val file = File.createTempFile("tmp",".java", directory)
      //converting source code to code KeY can use
      file.appendText(createFileContent(test.cfRoot))
      //proving the code using KeY
      val isProofSuccessful = KeyProver.proofFile(file)
      //file cleanup
      file.delete()
      directory.delete()

      /*
      println("*****")
      println(isProofSuccessful)
      println("*****")
       */
    }

  private fun createFileContent(ast: CompilationUnitTree?) : String {
    val sb = StringBuilder();

    return testCode
  }
}

  private class visitor<Void> () {

  }
}
