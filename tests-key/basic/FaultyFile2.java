import jatyc.lib.Typestate;

@Typestate("FaultyFile2.protocol")
class FaultyFile2 {

  public FileStatus open() {
    // :: warning: (FileStatus.OK: Shared{FileStatus})
    return FileStatus.OK;
  }

  public void hasNext() {
  }

  public boolean hasNext2() {
    return false;
  }

  public int read() {
    return -1;
  }

  public void close() {
  }

}
