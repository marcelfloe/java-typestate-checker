## Output without JML-contract

```
[...] INFO  KeyProver - Starting KeY example application.
[...] INFO  ProofSettings - Load proof dependent settings from file [...]\.key\proof-settings.json
[...] INFO  AbstractProblemLoader - Loading environment from [...]\Temp\key-temp4128845889666593376\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  KeyProver - Contract 'JML normal_behavior operation contract 0' of ClientCode::example is still open.
car6\ClientCode.java:18: error: Cannot call [setEcoDrive] on State{SUV, COMFORT_ON} | State{SUV, SPORT_ON}
    suv.setEcoDrive(false);
                   ^
1 error
```

## Output with JML contract

```
```
