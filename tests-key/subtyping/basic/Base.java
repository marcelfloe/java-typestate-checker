import mungo.lib.Typestate;
import java.util.Random;

@Typestate("Base.protocol")
public class Base {
  private Random rd = new Random();

  public boolean hasNext() {
    // :: warning: (this.rd: Shared{java.util.Random})
    return rd.nextBoolean();
  }

  public void next() {
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    System.out.println("Base calls next");
  }
}
