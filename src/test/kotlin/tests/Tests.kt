package tests

import org.junit.runners.Parameterized.Parameters
import java.io.File

private const val dir0 = "debug"
private const val dir1 = "basic"
private const val dir2 = "config"
private const val dir3 = "droppables"
private const val dir4 = "resolution"
private const val dir5 = "linked-list"
private const val dir6 = "linearity"
private const val dir7 = "exceptions"
private const val dir8 = "generics"
private const val dir9 = "subtyping"
private const val dir10 = "assignments"
private const val dir11 = "suppress-warnings"
private const val dir12 = "class-analysis"
private const val dir13 = "complex-flow"
private const val dir14 = "typestatetrees"
private const val dir15 = "cfg"

//tests for linked list and generics don't work
val ignore = listOf("linked-list", "generics"/*, dir9, dir14*/)
//val only = emptyList<String>()
val only = listOf(dir0, dir1, dir2, dir3, dir4, dir5, dir6, dir7)
//val only = listOf(dir8, dir9, dir10, dir11, dir12, dir13, dir14, dir15)

private val defaultOptsNoTypeInfo = arrayOf("-Anomsgtext", "-AtypestateTrees=disable")
private val defaultOpts = defaultOptsNoTypeInfo.plus("-AshowTypeInfo")

// A folder where we can make tests and narrow down an issue
class DebugTests(testFiles: List<File>) : PerDirectoryTest(
  dir0,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir0)
  }
}

class BasicTests(testFiles: List<File>) : PerDirectoryTest(
  dir1,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir1)
  }
}

class ConfigTest(testFiles: List<File>) : PerDirectoryTest(
  dir2,
  testFiles,
  defaultOpts.plus(arrayOf("-AconfigFile=tests/$dir2/jtc.config", "-Astubs=tests/$dir2/stubs", "-AstubWarnIfNotFound", "-Aignorejdkastub"))
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir2)
  }
}

class DroppablesTest(testFiles: List<File>) : PerDirectoryTest(
  dir3,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir3)
  }
}

class ResolutionTest(testFiles: List<File>) : PerDirectoryTest(
  dir4,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir4)
  }
}

class LinkedListTest(testFiles: List<File>) : PerDirectoryTest(
  dir5,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir5)
  }
}

class LinearityTest(testFiles: List<File>) : PerDirectoryTest(
  dir6,
  testFiles,
  defaultOptsNoTypeInfo
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir6)
  }
}

class ExceptionsTest(testFiles: List<File>) : PerDirectoryTest(
  dir7,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir7)
  }
}

class GenericsTest(testFiles: List<File>) : PerDirectoryTest(
  dir8,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir8)
  }
}

class SubtypingTest(testFiles: List<File>) : PerDirectoryTest(
  dir9,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir9)
  }
}

class AssignmentsTests(testFiles: List<File>) : PerDirectoryTest(
  dir10,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir10)
  }
}

class SuppressWarningsTests(testFiles: List<File>) : PerDirectoryTest(
  dir11,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir11)
  }
}

class ClassAnalysisTests(testFiles: List<File>) : PerDirectoryTest(
  dir12,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir12)
  }
}

class ComplexFlowTests(testFiles: List<File>) : PerDirectoryTest(
  dir13,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir13)
  }
}

class TypestateTreesTests(testFiles: List<File>) : PerDirectoryTest(
  dir14,
  testFiles,
  arrayOf("-Anomsgtext", "-AtypestateTrees=enable", "-AshowTypeInfo")
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir14)
  }
}

class CFGTests(testFiles: List<File>) : PerDirectoryTest(
  dir15,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir15)
  }
}
