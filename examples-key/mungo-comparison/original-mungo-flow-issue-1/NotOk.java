import java.util.*;

public class NotOk {
	public static void main(String[] args) {
		JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());

    loop: do {
      switch(it.hasNext()) {
        case True:
          System.out.println(it.next());
          continue loop;
        case False:
          break loop;
      }
    } while(false);
	}
}
