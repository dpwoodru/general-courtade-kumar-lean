import CKLaneN23.RSDefs

/-!
# Lane C, RA-stat: region split of `GammaNonCorner` (the union theorem consumed by N23b)

The split follows the coordinator's decision of 07:10Z:
* `GammaUTail S εc σ0` is owned by Lane R2. It covers all `b` with `u = b - d ≤ σ0 · b`.
* `GammaSmallB S εc b1 σ0` is owned by Lane C (v-mode contacts). It covers `b ≤ b1` with `σ0 · b ≤ u`.
* `GammaBulk S εc b1 σ0` is owned by Lane C (TM cell cover). It covers `b1 ≤ b` with `σ0 · b ≤ u`.

Each piece carries all hypotheses of `GammaNonCorner` plus its region restriction. The pieces overlap at equality.
-/

namespace CKLaneC.RSCell

open CKLaneN23.RS

/-- `u`-tail piece (Lane R2): `u = b - d ≤ σ0 · b`, all `b`. -/
def GammaUTail (S εc σ0 : ℝ) : Prop :=
  ∀ b t d : ℝ, 0 ≤ t → t ≤ 1 → 0 < d → d < b → b ≤ 1 / 2 → S < 2 * b - t * d → εc ≤ (1 / 2 - b) + d →
    b - d ≤ σ0 * b → 0 ≤ rayGamma b t d

/-- Small-`b` piece (Lane C): `b ≤ b1`, `σ0 · b ≤ u`. -/
def GammaSmallB (S εc b1 σ0 : ℝ) : Prop :=
  ∀ b t d : ℝ, 0 ≤ t → t ≤ 1 → 0 < d → d < b → b ≤ 1 / 2 → S < 2 * b - t * d → εc ≤ (1 / 2 - b) + d →
    b ≤ b1 → σ0 * b ≤ b - d → 0 ≤ rayGamma b t d

/-- Bulk piece (Lane C): `b1 ≤ b`, `σ0 · b ≤ u`. -/
def GammaBulk (S εc b1 σ0 : ℝ) : Prop :=
  ∀ b t d : ℝ, 0 ≤ t → t ≤ 1 → 0 < d → d < b → b ≤ 1 / 2 → S < 2 * b - t * d → εc ≤ (1 / 2 - b) + d →
    b1 ≤ b → σ0 * b ≤ b - d → 0 ≤ rayGamma b t d

/-- The union: the three pieces give `GammaNonCorner`. -/
theorem gammaNonCorner_of_pieces {S εc b1 σ0 : ℝ} (hu : GammaUTail S εc σ0) (hs : GammaSmallB S εc b1 σ0)
    (hb : GammaBulk S εc b1 σ0) : GammaNonCorner S εc := by
  intro b t d ht0 ht1 hd0 hdb hb12 hS hεc
  rcases le_total (b - d) (σ0 * b) with h2 | h2
  · exact hu b t d ht0 ht1 hd0 hdb hb12 hS hεc h2
  · rcases le_total b b1 with h1 | h1
    · exact hs b t d ht0 ht1 hd0 hdb hb12 hS hεc h1 h2
    · exact hb b t d ht0 ht1 hd0 hdb hb12 hS hεc h1 h2

end CKLaneC.RSCell
