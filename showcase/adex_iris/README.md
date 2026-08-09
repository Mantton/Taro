# AdEx Iris classifier

This package classifies the UCI Iris dataset with a recurrent adaptive
exponential integrate-and-fire network trained by e-prop. It is a numerical
compiler-correctness workload rather than a performance benchmark or general
machine-learning API.

## Run

The official dataset is pinned but not stored in Git:

```sh
make -C showcase/adex_iris prepare
taro run showcase/adex_iris --release -- \
  --data target/verifiers/adex_iris/6f608b71a7317216319b4d27b4d9bc84e6abd734eda7872b71a458569e2656c0/iris.data
make -C showcase/adex_iris verify
```

The verifier performs deterministic stratified five-fold cross-validation and
requires at least 135 of 150 held-out predictions. The reference result is
142/150 with confusion matrix:

```text
50  0  0
 0 44  6
 0  2 48
```

## Model

Four train-normalized measurements become deterministic 20–200 Hz spike
trains. They drive 16 recurrent regular-spiking AdEx neurons and three leaky
readouts over 50 ms at a 0.5 ms step. Each neuron owns its incoming input and
recurrent synapses; each readout owns its output synapses. The connections are
trained for 80 epochs with symmetric-feedback e-prop and Adam.

Each synapse retains voltage and adaptation eligibility components. The hard
spike/reset transition uses a triangular surrogate derivative only for the
local eligibility recurrence; no activation history or BPTT tape is stored.

The neuron parameters follow Brette and Gerstner's regular-spiking AdEx model.
The dataset is [UCI Iris](https://doi.org/10.24432/C56C76), licensed CC BY 4.0.

## Compiler coverage and findings

| Coverage | Regression or check |
| --- | --- |
| Diverging branches in desugared `while` loops | [`flow.tr`](../../language_tests/source_files/valid/flow.tr) |
| Nested generic collections and mutable projections | Dataset/fold tests |
| Dense floating-point loops and `exp`/`log` intrinsics | AdEx and training tests |
| Debug/release numerical agreement | `make -C showcase/adex_iris verify` smoke comparison |
| Nested neuron and synapse mutation across collecting calls | Network determinism and full verification |

The workload found and fixed type inference for a desugared `while` whose body
and synthetic exit branch both have the never type. Taro does not currently
provide locale-independent floating-point formatting, so the CLI renders its
small metric values with a fixed nine-place decimal encoder.

## Limits

The implementation is single-threaded, dense, current-based, and fixed to one
experiment. It does not provide model persistence, SIMD, autodiff, random
feedback, conductance synapses, or a public SNN library.
