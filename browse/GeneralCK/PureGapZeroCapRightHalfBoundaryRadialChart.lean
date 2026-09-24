import GeneralCK.PureGapZeroCapRightStationaryFullRadialChart

/-! The exact right-cap value chart includes the maximal second entropy
cap `b=1/2`. The derivative owner is separate at that boundary. -/

namespace GeneralCK

theorem canonicalPureGap_rightCap_full_radial_eq_le_half {u a b : ℝ}
    (hu : 0 < u) (hua : u < a) (hab : a < b) (hb : b ≤ 1 / 2) :
    canonicalPureGap a b (H u) (H b) =
      interiorCost u b +
        F (b - a) ((H u + H b) / 2) -
        F (b - u) ((H u + H b) / 2) +
        F (1 - a - b) ((H u + H b) / 2) -
        eta ((H u + H b) / 2) +
        (eta (H u) - F (1 - 2 * a) (H u)) / 2 := by
  have huHalf : u ≤ 1 / 2 := (hua.trans hab).le.trans hb
  have hcorr : entropyCorrection (H u) (H b) =
      interiorCost u b - F (b - u) ((H u + H b) / 2) := by
    simp only [entropyCorrection, atomCorrection,
      entropyInverse_H_lower hu.le huHalf,
      entropyInverse_H_lower (hu.trans (hua.trans hab)).le hb]
    rw [abs_of_nonpos (by linarith : u - b ≤ 0)]
    ring
  have hright : radialPhi (1 - 2 * b) (H b) = 0 := by
    simpa [radialPhi, phi, abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * b)]
      using phi_at_entropy_cap (hu.trans (hua.trans hab)) hb
  rw [canonicalPureGap, hcorr, hright]
  simp only [radialPhi]
  ring

#print axioms canonicalPureGap_rightCap_full_radial_eq_le_half

end GeneralCK
