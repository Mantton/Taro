# AdEx Iris verifier

This verifier pins the official UCI Iris archive and runs the deterministic
AdEx/e-prop showcase. Dataset preparation is the only networked step.

```sh
make -C showcase/adex_iris prepare
make -C showcase/adex_iris verify
```

The prepared `iris.data` is stored under `target/verifiers/adex_iris/` and is
never committed. Verification checks all 150 held-out predictions, finite
state, the confusion matrix, and the fixed 90% accuracy gate.
