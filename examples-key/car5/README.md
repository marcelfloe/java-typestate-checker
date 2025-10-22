## Output without KeY
```
ClientCode.java:18: error: Cannot call [switchMode] on State{SUV, COMFORT_ON} | State{SUV, OFF}
    suv.switchMode();
                  ^
ClientCode.java:19: error: Cannot call [setFourWheels] on State{SUV, COMFORT_ON} | State{SUV, SPORT_ON}
    suv.setFourWheels(true);
                     ^
2 errors
```

## Output without JML-contract

```
[stub classes]
[...] INFO  KeyProver - Starting KeY example application.
[...] INFO  ProofSettings - Load proof dependent settings from file ...\proof-settings.json
[...] INFO  AbstractProblemLoader - Loading environment from ...\Temp\key-temp436502371325413411\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  AbstractProblemLoader - Loading environment from ...\Temp\key-temp436502371325413411\source
[...] INFO  AbstractProblemLoader - Creating init config
[...] INFO  KeyProver - Contract 'JML normal_behavior operation contract 0' of ClientCode::example is still open.
[...] INFO  KeyProver - Contract could not be proven!
[class with method implementation]
ClientCode.java:19: error: Cannot call [setFourWheels] on State{SUV, COMFORT_ON} | State{SUV, SPORT_ON}
    suv.setFourWheels(true);
                     ^
ClientCode.java:18: error: Cannot call [switchMode] on State{SUV, COMFORT_ON} | State{SUV, OFF}
    suv.switchMode();
                  ^
2 errors
```

## Output with JML contract

```
Identical to output above.
Manual proving required.
```
