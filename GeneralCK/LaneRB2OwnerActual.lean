import GeneralCK.Certificates.LaneRB2WaveV2.Coverage
import GeneralCK.CorrectionFamilyAssembly

/-!
# Lane R-B2 — `hC2` AT THE TYPE THE CANONICAL CONSUMER ACTUALLY TAKES

## Why this file exists

`GeneralCK/LaneRB2Owner.lean` proves
`GeneralCK.Correction.Complement.SignsOnBox (1 / 10) (1 / 5) (1 / 10) 1`, which is the exact
target this lane was assigned, and it is closed and loadable. **It does not fill the `hC2`
slot of the canonical consumer.**

Canonical source, `GeneralCK/CorrectionComplementCharts.lean`
sha `ba3e849670a3f2d6df328e360fc470bb487c9db077249ff75165f4cf2f76523c`, 6,843 B, line 46:
```
theorem full_ratio_signs_of_charts
    (hC2 : ActualRatioFamilyOn (1/10) (1/5) (1/10) 1)
```
and identically at `CorrectionComplementLedger.lean:93` and `:115`.

The two predicates differ in STRENGTH, not merely in spelling:
```
ActualRatioMinorsPositive u rho  :=  0 < Mleft … ∧ 0 < Mdet …     STRICT
RatioSigns                u rho  :=  0 < Mleft … ∧ 0 ≤ Mdet …     WEAK
ratioSigns_of_positive : ActualRatioMinorsPositive → RatioSigns := ⟨h.1, h.2.le⟩
```
The canonical bridge runs strict → weak only. `0 ≤ Mdet` does not recover `0 < Mdet`, so
`SignsOnBox → ActualRatioFamilyOn` is underivable. Demonstrated, not asserted: the negative
probe `LaneRB2BindNeg.lean` fails with
`has type Complement.RatioSigns … but is expected to have type ActualRatioMinorsPositive …`
while its four side conditions resolve, so the box shape was never the problem.

## Why the repair costs nothing

`Coverage.coverage` proves the STRICT pair under exactly `ActualRatioFamilyOn`'s hypotheses —
`u ∈ Icc u0 u1 → rho ∈ Icc r0 r1 → rho < 1`. Its conclusion **is**
`ActualRatioMinorsPositive` definitionally. The strictness was certified by all 11,784 cells
from the start; the adapter this lane was handed, `signsOnBox_of_strict_owner`, discarded it —
a fact its own name records.

🔴 The eta-expansion remains load-bearing for the same reason as in the owner:
`ActualRatioFamilyOn` binds `⦃u rho⦄` strict-implicit and `coverage` binds `{u rho}`
ordinary-implicit, and Lean will not insert that conversion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace GeneralCK.Certificates.LaneRB2Owner

open Set GeneralCK GeneralCK.Correction

/-- **`hC2` at the type the canonical consumer takes.** Unconditional. -/
theorem hC2_actual : GeneralCK.Correction.ActualRatioFamilyOn (1 / 10) (1 / 5) (1 / 10) 1 :=
  fun _ _ hu hr hr1 => GeneralCK.Certificates.LaneRB2WaveV2.coverage hu hr hr1

/-- **GATE 12 SECOND CLAUSE**, fully unfolded, transcribed from `CorrectionFamilyAssembly.lean`
lines 16 and 23. If `ActualRatioFamilyOn` or `ActualRatioMinorsPositive` ever meant something
other than what is written here, this would not typecheck. -/
theorem hC2_actual_unfolded :
    ∀ ⦃u rho : ℝ⦄, u ∈ Icc (1 / 10 : ℝ) (1 / 5 : ℝ) →
      rho ∈ Icc (1 / 10 : ℝ) (1 : ℝ) → rho < 1 →
      0 < Mleft (H u) (H (u + rho * (1 / 2 - u))) ∧
      0 < Mdet (H u) (H (u + rho * (1 / 2 - u))) :=
  hC2_actual

/-- **NON-VACUITY**, strict interior of both coordinates. -/
theorem hC2_actual_witness :
    GeneralCK.Correction.ActualRatioMinorsPositive (3 / 20) (1 / 2) :=
  hC2_actual (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)

/-- 🔑 **THE SEMANTIC BINDING PROBE THE RULING REQUIRES**, in the form it specifies:
`example : ExactExpectedProp := Candidate.theorem`, with `ExactExpectedProp` copied from the
canonical consumer's own hypothesis line rather than restated. -/
example : GeneralCK.Correction.ActualRatioFamilyOn (1 / 10) (1 / 5) (1 / 10) 1 := hC2_actual

#check @hC2_actual
#check @hC2_actual_unfolded
#check @hC2_actual_witness

#print axioms hC2_actual
#print axioms hC2_actual_unfolded
#print axioms hC2_actual_witness

end GeneralCK.Certificates.LaneRB2Owner
