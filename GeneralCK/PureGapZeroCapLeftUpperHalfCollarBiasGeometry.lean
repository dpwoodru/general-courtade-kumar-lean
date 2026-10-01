import GeneralCK.PureGapZeroCapLeftUpperHalfCollarQuartic

/-!
Actual-law bias containment used in the proposed left-upper real-series
half-collar remainder. The entropy inverse and radial contact remain the
project's sInf definitions; no power-series premise is used here.
-/

namespace GeneralCK

theorem leftUpper_halfEntropyInverse_between {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    a ≤ entropyInverse ((H a + H b) / 2) ∧
      entropyInverse ((H a + H b) / 2) ≤ b := by
  have haHalf : a ≤ 1 / 2 := hab.trans hb
  have hb0 : 0 ≤ b := ha.trans hab
  have hHa : 0 ≤ H a := H_nonneg ha (by linarith)
  have hHb : 0 ≤ H b := H_nonneg hb0 (by linarith)
  have horder : H a ≤ H b :=
    H_strictMonoOn.monotoneOn ⟨ha, haHalf⟩ ⟨hb0, hb⟩ hab
  have hmid0 : 0 ≤ (H a + H b) / 2 := by linarith
  have hmid1 : (H a + H b) / 2 ≤ 1 := by
    have h1 := H_le_one b
    linarith
  constructor
  · simpa only [entropyInverse_H_lower ha haHalf] using
      (entropyInverse_mono hHa hmid1 (by linarith : H a ≤ (H a + H b) / 2))
  · simpa only [entropyInverse_H_lower hb0 hb] using
      (entropyInverse_mono hmid0 (H_le_one b)
        (by linarith : (H a + H b) / 2 ≤ H b))

theorem leftUpper_radialContact_bias_upper {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) :
    1 / 2 - radialContact r h ≤ r / (2 * h) := by
  let v := radialContact r h
  have heq : r * H v = h * (1 - 2 * v) := radialContact_equation hr hh
  have hH : H v ≤ 1 := H_le_one v
  have hbound : h * (1 - 2 * v) ≤ r := by
    rw [← heq]
    nlinarith [hH]
  apply (le_div_iff₀ (by positivity : 0 < 2 * h)).2
  dsimp [v] at *
  nlinarith

#print axioms leftUpper_halfEntropyInverse_between
#print axioms leftUpper_radialContact_bias_upper

end GeneralCK
