import mungo.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("FileWrapperProtocol")
class NotOkFileWrapper2 {

  private @Nullable File file = null;

  public void init(File file) {
    this.file = file;
  }

  public String read() {
    return file.read();
  }

  public void close() {

  }

}
