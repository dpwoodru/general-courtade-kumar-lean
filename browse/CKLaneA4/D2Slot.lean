import CKLaneA4.D2Cover
import GeneralCK.CorrectionComplementCharts
import GeneralCK.CorrectionComplementLedger
import GeneralCK.CorrectionCertifiedBandClosure

/-!
# Lane A4: closed owner of the `ChartOwners.diagonal2` slot

`diagonal2 : SignsOnBox (1/10) (1/5) 0 (1/10)`, i.e. `u ∈ [1/10, 1/5]`, `rho ∈ (0, 1/10]`.

The 256 cells of Lane A's certificate (`A/gen/trees/diagonal2.json`) are each checked by one kernel
evaluation of Lane A's `CKLaneA.Cell.cellOK` and assembled in `CKLaneA4.D2Cover.slot_covered`.
`rho = 0` is included in the cells (the program outputs `D` and `m11` stay positive there), while
`kdet = (w-u)^2 D` degenerates at `rho = 0`; the strict `0 < rho` needed by `actual_of_prog` comes
from the `SignsOnBox` binders.
-/

namespace CKLaneA4.D2
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement CKLaneA.Cell CKLaneA.Prog

/-- strict actual minors on `[1/10, 1/5] × (0, 1/10]` -/
theorem diagonal2_actual : ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc (1 / 10 : ℝ) (1 / 5) →
    rho ∈ Set.Ioc (0 : ℝ) (1 / 10) → ActualRatioMinorsPositive u rho := by
  intro u rho hu hr
  obtain ⟨hD, hM⟩ := slot_covered.apply (a := u) (z := rho)
    (by push_cast; linarith [hu.1]) (by push_cast; linarith [hu.2])
    (by push_cast; linarith [hr.1]) (by push_cast; linarith [hr.2])
  exact actual_of_prog (by linarith [hu.1]) (by linarith [hu.2]) hr.1 (by linarith [hr.2]) hD hM

/-- `ChartOwners.diagonal2` field type -/
theorem diagonal2_signs : SignsOnBox (1 / 10) (1 / 5) 0 (1 / 10) := by
  intro u rho _ _ hr _ hub hrb
  exact ratioSigns_of_positive (diagonal2_actual hub ⟨hr, hrb.2⟩)

/-- exact-type check: `diagonal2_signs` fills the `diagonal2` field of `ChartOwners` -/
example (C : ChartOwners) : ChartOwners := { C with diagonal2 := diagonal2_signs }

/-- the `1/10 < u ≤ 1/5, rho < 1/10` arm of `OutsideCertifiedC1C2Region`, strict form -/
theorem diagonal2_arm : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    1 / 10 < u → u ≤ 1 / 5 → rho < 1 / 10 → ActualRatioMinorsPositive u rho := by
  intro u rho _ _ hr _ h10 h5 h1
  exact diagonal2_actual ⟨h10.le, h5⟩ ⟨hr, h1.le⟩

/-- `RemainingOwners.lowRatioC2` field type -/
theorem lowRatioC2_owner : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    LowRatioC2 u rho → RatioSigns u rho := by
  intro u rho _ _ hr _ h
  exact ratioSigns_of_positive (diagonal2_actual ⟨h.1.le, h.2.1⟩ ⟨hr, h.2.2.le⟩)

end CKLaneA4.D2
