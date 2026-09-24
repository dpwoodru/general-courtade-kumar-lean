import GeneralCK.CorrectionHighUScaledContract

/-!
# Source-only two-wedge target for the correction high-u corner

The raw lower bounds split at `rho=t` and avoid dividing by powers
that vanish on the open coordinate faces. No bound is proved here.
-/

namespace GeneralCK.Correction.HighU

def NearCornerRawWedgeTarget : Prop :=
  ∀ t rho : ℝ, 0 < t → t ≤ 1 / 100 → 0 < rho → rho ≤ 1 / 100 →
    t ^ 2 / 2 ≤ Natural.m11 (1 / 2 - t) (1 / 2 - (1 - rho) * t) ∧
    (rho ≤ t →
      2 * rho ^ 2 * t ^ 9 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t)) ∧
    (t ≤ rho →
      2 * rho ^ 4 * t ^ 7 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t))

end GeneralCK.Correction.HighU
