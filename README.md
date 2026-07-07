# Lean proofs

Formal verification of *Temporal Conductance and Bounds on the Voter Model for Dynamic Networks*.
Lean and Mathlib versions are pinned in `lean-toolchain` and `lake-manifest.json`.

## Review cone

Please look at the [review cone](https://anonymous.4open.science/w/temporal-conductance/)
if you want to review how we formalized the *statements* of the main theorems in Lean.

## Setup

Install [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager);
it reads `lean-toolchain` and fetches the right Lean version automatically.

## Build

From this directory:

```sh
lake exec cache get   # download prebuilt Mathlib (skip the ~1h rebuild)
lake build            # build all seven libraries
```

