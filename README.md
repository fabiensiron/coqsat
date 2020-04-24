# CoqSat

CoqSat is a ``Coq`` implementation of a basic Sat algorithm with soundness proof. Its goal is only pedagogical.

## Installation

To build:
```bash
source env_win32.sh # if on win32 via linux subsystem
./configure.sh # generate makefile with coq_makefile
make
```
I recommand using ``proof-general``, the emacs plugin. Tested with ``Coq`` 8.8.2.

## Usage

```coq
Require Import Formula.

Definition X := Var 0.
Definition Y := Var 1.

Definition ex :=
  And (Or X (Negate Y))
      (Or (Negate X) Y).

Definition model : valuation :=
  update_valuation
    (update_valuation empty_valuation 0 true)
    1 true.


Compute (simplify_and_valuate model ex).

Require Import Solver.

Compute (solver ex).
```

## TODO
- DPLL solver and soundness
- use it as an ocaml library

## License
[Beerware](https://en.wikipedia.org/wiki/Beerware)
