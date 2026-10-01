# comparator check

[comparator](https://github.com/leanprover/comparator) checks that `CKChallenge.Solution` proves exactly the statement
of the trusted challenge `CKChallenge.Challenge`, with no axioms beyond `propext`, `Quot.sound` and `Classical.choice`,
and replays the solution's whole environment (Mathlib included) through the Lean kernel.

- `CKChallenge/Defs.lean` and `CKChallenge/Challenge.lean`: the Courtade–Kumar statement as written for Formal
  Conjectures ([google-deepmind/formal-conjectures#6688](https://github.com/google-deepmind/formal-conjectures/pull/6688)),
  with the Formal Conjectures attributes removed and explicit Mathlib imports. The challenge imports only Mathlib and
  `CKChallenge.Defs`.
- `CKChallenge/Bridge.lean`: `GeneralCK.GeneralCourtadeKumar` implies the challenge statement (the two sets of
  definitions have identical bodies).
- `CKChallenge/Solution.lean`: the challenge theorem, proved from the final theorem.
- `config.json`: the comparator configuration.

These modules form the library `CKChallenge` of the root Lake project (`srcDir = "verification/comparator"`); it is not
part of the default build target. Commands and status: [`HOW_TO_VERIFY.md`](../../HOW_TO_VERIFY.md), Step 3.
