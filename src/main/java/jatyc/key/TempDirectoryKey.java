package jatyc.key;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

/**
 * Class which handles the Files used by KeY.
 * <p>
 * This class currently allows for multiple files to be replaced.
 * However, this is not required, as only one contract needs proving per error message being checked.
 */
public class TempDirectoryKey {

  private static Path tempDirectory = null; //holds the sourceDirectory and copyDirectory
  private static Path sourceDirectory = null; //holds the source directory used by KeY
  private static Path copyDirectory = null; //holds files which were replaced to perform a proof

  public TempDirectoryKey() {
    try {
      tempDirectory = Files.createTempDirectory("key-temp");
      tempDirectory.toFile().deleteOnExit();
      sourceDirectory = Files.createDirectory(new File(tempDirectory.toString() + "\\source").toPath());
      sourceDirectory.toFile().deleteOnExit();
      copyDirectory = Files.createDirectory(new File(tempDirectory.toString() + "\\copy").toPath());
      copyDirectory.toFile().deleteOnExit();
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  public void replaceFileForProof(String prefix, String suffix, String content, List<String> relativePathNames)
    throws IOException {
    String relativePath = "";
    if (relativePathNames != null && !relativePathNames.isEmpty()) {
      for (String relativePathName : relativePathNames) {
        if (relativePathName.isBlank()) continue;
        relativePath = relativePath + "\\" + relativePathName;
      }
    }
    relativePath = relativePath + "\\" + prefix + "." + suffix;
    if (Files.exists(new File(copyDirectory + relativePath).toPath())) throw new IllegalArgumentException("File already got replaced: " + sourceDirectory + relativePath);
    if (!new File(sourceDirectory + relativePath).renameTo(new File(copyDirectory + relativePath))) throw new IOException("Could not rename old file: " + sourceDirectory + relativePath);
    putFile(prefix, suffix, content, relativePathNames);
  }

  public void putFile(String prefix, String suffix, String content, List<String> relativePathNames)
    throws IOException {
    String relativePath = "";
    if (relativePathNames != null && !relativePathNames.isEmpty()) {
      for (String relativePathName : relativePathNames) {
        if (relativePathName.isBlank()) continue;
        relativePath = relativePath + "\\" + relativePathName;
        File sourceDir = new File(sourceDirectory.toString() + relativePath);
        sourceDir.mkdir();
        sourceDir.deleteOnExit();
        File copyDir = new File(copyDirectory.toString() + relativePath);
        copyDir.mkdir();
        copyDir.deleteOnExit();
      }
    }
    String absolutePath = sourceDirectory.toString() + relativePath + "\\" + prefix + "." + suffix;
    File file = new File(absolutePath);
    if (file.exists()) throw new IllegalArgumentException("File already exists: " + absolutePath);
    file.createNewFile();
    FileWriter fileWriter = new FileWriter(file);
    fileWriter.write(content);
    fileWriter.close();
    file.deleteOnExit();
  }

  public void undoReplacements() {
    //multiple files might need replacement due to inheritance
    // ^ actually not required, as the parent contract is copied to the child contract and only the child contract is being proven
    try {
      undoReplacementsDir(copyDirectory.toFile(), "");
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  private void undoReplacementsDir(File dir, String relativePath) throws IOException {
    for (File file : dir.listFiles()) {
      String newRelativePath = relativePath + "\\" + file.getName();
      if (file.isDirectory()) {
        undoReplacementsDir(file, newRelativePath);
      } else {
        undoReplacementsFile(file, newRelativePath);
      }
    }
  }

  private void undoReplacementsFile(File file, String relativePath) throws IOException {
    String targetPath = sourceDirectory.toString() + relativePath;
    if (!new File(targetPath).delete()) throw new IOException("Could not delete file: " + targetPath);
    if (!file.renameTo(new File(targetPath))) throw new IOException("Could not rename file: " + file.getName());
    file.deleteOnExit();
  }

  public File getSourceDir() {
    return sourceDirectory.toFile();
  }
}
