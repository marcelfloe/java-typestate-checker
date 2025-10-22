## Output without KeY
```
ClientCode.java:17: error: Cannot call [switchMode] on State{SUV, COMFORT_ON} | State{SUV, OFF}
    suv.switchMode();
                  ^
1 error
```

## Output without JML-contract

```
[...] INFO  KeyProver - Starting KeY example application.
[...] INFO  ProofSettings - Load proof dependent settings from file C:...\proof-settings.json
[...] INFO  AbstractProblemLoader - Loading environment from ...\Temp\key-temp9453474928315630392\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  AbstractProblemLoader - Loading environment from ...\Temp\key-temp9453474928315630392\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] WARN  ApplyStrategy - doWork exceptionde.uka.ilkd.key.util.AssertionFailure: Assertion failed: The sort of self was supposed to be a subsort of self's, but are Car and SUV.
[...]
[...] INFO  KeyProver - Contract 'JML normal_behavior operation contract 0' of ClientCode::example is still open.
[...] INFO  KeyProver - Contract could not be proven!
[...]
ClientCode.java:17: error: Cannot call [switchMode] on State{SUV, COMFORT_ON} | State{SUV, OFF}
    suv.switchMode();
                  ^
1 error
```

## Output with JML contract

```
Identical to output above due to KeY throwing an exception.
Manual proving required.
```
