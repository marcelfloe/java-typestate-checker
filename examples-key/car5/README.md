## Output without JML-contract

```[12:16:26.477] INFO  KeyProver - Starting KeY example application.
[...] INFO  ProofSettings - Load proof dependent settings from file [...]\proof-settings.json
[...] INFO  AbstractProblemLoader - Loading environment from [...]\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  AbstractProblemLoader - Loading environment from [...]\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  KeyProver - Contract not found: ClientCode.example()
car4\ClientCode.java:8: error: Cannot call [switchMode] on State{SUV, COMFORT_ON} | State{SUV, OFF}
    suv.switchMode();
                  ^
1 error
```

## Output with JML contract

```
```
