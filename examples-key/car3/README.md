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
[...] INFO  ProofSettings - Load proof dependent settings from file ...\proof-settings.json
[...] INFO  AbstractProblemLoader - Loading environment from ...\Temp\key-temp2393677558983102466\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  AbstractProblemLoader - Loading environment from ...\Temp\key-temp2393677558983102466\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  KeyProver - Contract 'JML normal_behavior operation contract 0' of ClientCode::example is still open.
[...] INFO  KeyProver - Contract could not be proven!
ClientCode.java:17: error: Cannot call [switchMode] on State{SUV, COMFORT_ON} | State{SUV, OFF}
    suv.switchMode();
                  ^
1 error
```

## Output with JML contract

```
[...] INFO  KeyProver - Starting KeY example application.
[...] INFO  ProofSettings - Load proof dependent settings from file ...\proof-settings.json
[...] INFO  AbstractProblemLoader - Loading environment from ...\Temp\key-temp8401910787855772120\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  AbstractProblemLoader - Loading environment from ...\Temp\key-temp8401910787855772120\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  KeyProver - Contract 'JML normal_behavior operation contract 0' of ClientCode::example is verified.
[...] INFO  KeyProver - Contract proven, no error!
```
