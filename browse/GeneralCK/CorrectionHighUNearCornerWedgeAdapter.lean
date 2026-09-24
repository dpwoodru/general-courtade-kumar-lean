import GeneralCK.CorrectionHighUNearCornerWedgeTarget

/-!
The source-only wedge certificate target implies quantitative scaled margins.
The theorem remains conditional on the two raw wedge inequalities.
-/

namespace GeneralCK.Correction.HighU

theorem nearCorner_scaled_margins_of_raw_wedges
    (h : NearCornerRawWedgeTarget) {t rho : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    (1 / 2 : ℝ) ≤
      Natural.m11 (1 / 2 - t) (1 / 2 - (1 - rho) * t) / t ^ 2 ∧
    (1 : ℝ) ≤
      Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t) /
        (rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2)) := by
  obtain ⟨hm, hkSmall, hkLarge⟩ := h t rho ht ht1 hr hr1
  have ht2 : 0 < t ^ 2 := by positivity
  have hden : 0 < rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2) := by positivity
  constructor
  · apply (le_div_iff₀ ht2).2
    nlinarith only [hm]
  · apply (le_div_iff₀ hden).2
    rcases le_total rho t with hrt | htr
    · have hsq : rho ^ 2 ≤ t ^ 2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hrt)
          (add_nonneg ht.le hr.le)]
      have hsum : t ^ 2 + rho ^ 2 ≤ t ^ 2 + t ^ 2 :=
        by simpa [add_comm] using add_le_add_left hsq (t ^ 2)
      have hfactor : 0 ≤ rho ^ 2 * t ^ 7 := by positivity
      have hdenBound := mul_le_mul_of_nonneg_left hsum hfactor
      have hdenBound' :
          rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2) ≤
            2 * rho ^ 2 * t ^ 9 := by
        calc
          rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2)
              ≤ rho ^ 2 * t ^ 7 * (t ^ 2 + t ^ 2) := hdenBound
          _ = 2 * rho ^ 2 * t ^ 9 := by ring
      simpa only [one_mul] using hdenBound'.trans (hkSmall hrt)
    · have hsq : t ^ 2 ≤ rho ^ 2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr htr)
          (add_nonneg ht.le hr.le)]
      have hsum : t ^ 2 + rho ^ 2 ≤ rho ^ 2 + rho ^ 2 :=
        by simpa [add_comm] using add_le_add_right hsq (rho ^ 2)
      have hfactor : 0 ≤ rho ^ 2 * t ^ 7 := by positivity
      have hdenBound := mul_le_mul_of_nonneg_left hsum hfactor
      have hdenBound' :
          rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2) ≤
            2 * rho ^ 4 * t ^ 7 := by
        calc
          rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2)
              ≤ rho ^ 2 * t ^ 7 * (rho ^ 2 + rho ^ 2) := hdenBound
          _ = 2 * rho ^ 4 * t ^ 7 := by ring
      simpa only [one_mul] using hdenBound'.trans (hkLarge htr)

#print axioms nearCorner_scaled_margins_of_raw_wedges

end GeneralCK.Correction.HighU
