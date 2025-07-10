import mungo.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("FileWrapperProtocol")
class NotOkFileWrapper1 {

  private @Nullable File file = null;

  public void init(File file) {}

  public String read() {
    return file.read();
  }

  public void close() {
    file.close();
  }

}
