## Mungo's output

```

Main.java: 0-0: Semantic Error
		Object created at Main.java: 5. Typestate mismatch. Found: end, Boolean hasNext(). Expected: Boolean hasNext().```

## Our tool's output

```
Main.java:8: error: Cannot call [hasNext] on State{JavaIterator, HasNext} | State{JavaIterator, Next} | State{JavaIterator, end}
      switch(it.hasNext()) {
                       ^
Main.java:10: error: Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end}
          System.out.println(it.next());
                                    ^
Main.java:4: error: [it] did not complete its protocol (found: State{JavaIterator, Next} | State{JavaIterator, end})
	public static void main(String[] args) {
	                   ^
JavaIterator.java:18: error: Incompatible return value: cannot cast from Shared{java.lang.Object} | Null to Shared{java.lang.String}
    return it.next();
    ^
4 errors```
