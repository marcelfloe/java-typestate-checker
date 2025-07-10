## Mungo's output

```

NotOk.java: 5-14: Semantic Error
		Object created at NotOk.java: 5. Typestate mismatch. Found: end. Expected: String read(), void close().

NotOk.java: 9-14: Semantic Error
		Object created at NotOk.java: 9. Typestate mismatch. Found: end. Expected: String read(), void close().```

## Our tool's output

```
Ok.java:14: error: Cannot call [read] on Shared{File}
    System.out.println(f.read());
                             ^
Ok.java:10: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{File}
    use(f);
        ^
NotOk.java:10: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{File}
    use(f);
        ^
NotOk.java:4: error: [f] did not complete its protocol (found: State{File, Read})
  public static void main1() {
                     ^
4 errors```
