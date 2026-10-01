import GeneralCK.PureGapEntropyRearrangement

/-!
# Canonical formula for the retained pure gap

This identifies the project definition of `pureGap` with the manuscript's
explicit lower-half four-variable function `G` on its canonical mean chart.
-/

namespace GeneralCK

/-- The explicit retained pure gap on sorted lower-half means. -/
noncomputable def canonicalPureGap (a c e f : ℝ) : ℝ :=
  F (c - a) ((e + f) / 2) + entropyCorrection e f -
    radialPhi (1 - a - c) ((e + f) / 2) +
    (radialPhi (1 - 2 * a) e + radialPhi (1 - 2 * c) f) / 2

/-- Exact identification of `pureGap` with the manuscript's canonical `G`. -/
theorem pureGap_eq_canonicalPureGap {a c e f : ℝ}
    (hac : a ≤ c) (hc : c ≤ 1 / 2) :
    pureGap a c e f = canonicalPureGap a c e f := by
  have hac' : a - c ≤ 0 := sub_nonpos.mpr hac
  have hcenter : 0 ≤ 1 - a - c := by linarith
  have haRad : 0 ≤ 1 - 2 * a := by linarith
  have hcRad : 0 ≤ 1 - 2 * c := by linarith
  unfold pureGap fourMomentLowerBound candidateGap canonicalPureGap phi radialPhi
  rw [abs_of_nonpos hac', abs_of_nonneg haRad, abs_of_nonneg hcRad,
    abs_of_nonneg (show 0 ≤ 1 - 2 * ((a + c) / 2) by linarith)]
  ring

/-- The global positive-entropy pure-gap theorem follows from nonnegativity
of the explicit canonical `G` on the ordered marginal-physical chamber. -/
theorem pureGap_nonneg_of_canonicalPureGap
    (hG : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ canonicalPureGap a c e f)
    {a b e f : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (he : 0 < e) (hf : 0 < f)
    (hecap : e ≤ H a) (hfcap : f ≤ H b) : 0 ≤ pureGap a b e f := by
  apply pureGap_nonneg_of_sorted_lower_half_ordered_entropy_feasible
    (a := a) (b := b) (e := e) (f := f) _ ha₀ ha₁ hb₀ hb₁ he hf hecap hfcap
  intro x y g h hx hxy hy hg hgh hgcap hhcap
  rw [pureGap_eq_canonicalPureGap hxy hy]
  exact hG x y g h hx hxy hy hg hgh hgcap hhcap

end GeneralCK
