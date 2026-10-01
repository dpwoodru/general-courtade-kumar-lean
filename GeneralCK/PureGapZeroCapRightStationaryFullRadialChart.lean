import GeneralCK.PureGapCapZeroReduction
import GeneralCK.PureGapMeanStationarity

/-!
# Full right-cap radial chart and the maximal-entropy obstruction

At a positive second cap, write the two entropy coordinates as `H u,H b`.
The free first mean is `a`, with `u<a<b<1/2`.  The value and derivative
below use the actual project profiles.  The two radii in the derivative
coincide precisely at `b=1/2`, explaining why the `f=1` chart is a
special case rather than a direct owner for `f<1`.
-/

namespace GeneralCK

/-- Exact value on the right cap's strict three-mean chamber. -/
theorem canonicalPureGap_rightCap_full_radial_eq {u a b : ℝ}
    (hu : 0 < u) (hua : u < a) (hab : a < b) (hb : b < 1 / 2) :
    canonicalPureGap a b (H u) (H b) =
      interiorCost u b +
        F (b - a) ((H u + H b) / 2) -
        F (b - u) ((H u + H b) / 2) +
        F (1 - a - b) ((H u + H b) / 2) -
        eta ((H u + H b) / 2) +
        (eta (H u) - F (1 - 2 * a) (H u)) / 2 := by
  have huHalf : u ≤ 1 / 2 := (hua.trans (hab.trans hb)).le
  have hbHalf : b ≤ 1 / 2 := hb.le
  have hcorr : entropyCorrection (H u) (H b) =
      interiorCost u b - F (b - u) ((H u + H b) / 2) := by
    simp only [entropyCorrection, atomCorrection,
      entropyInverse_H_lower hu.le huHalf,
      entropyInverse_H_lower (hu.trans (hua.trans hab)).le hbHalf]
    rw [abs_of_nonpos (by linarith : u - b ≤ 0)]
    ring
  have hright : radialPhi (1 - 2 * b) (H b) = 0 := by
    simpa [radialPhi, phi, abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * b)]
      using phi_at_entropy_cap (hu.trans (hua.trans hab)) hbHalf
  rw [canonicalPureGap, hcorr, hright]
  simp only [radialPhi]
  ring

/-- Exact first-mean derivative along the full right cap. -/
theorem deriv_canonicalPureGap_rightCap_full_radial {u a b : ℝ}
    (hu : 0 < u) (hua : u < a) (hab : a < b) (hb : b < 1 / 2) :
    deriv (fun x => canonicalPureGap x b (H u) (H b)) a =
      -deriv (fun r => F r ((H u + H b) / 2)) (b - a) -
        deriv (fun r => F r ((H u + H b) / 2)) (1 - a - b) +
        deriv (fun r => F r (H u)) (1 - 2 * a) := by
  have hHu : 0 < H u := H_pos hu (by linarith)
  have hHb : 0 < H b := H_pos (hu.trans (hua.trans hab)) (by linarith)
  exact deriv_canonicalPureGap_left hab (by linarith) (by linarith) hHu hHb

/-- The two first-mean radial arguments merge only at the maximal
second cap.  For every strict `b<1/2` they are distinct. -/
theorem rightCap_stationary_radii_eq_iff_half (a b : ℝ) :
    b - a = 1 - a - b ↔ b = 1 / 2 := by
  constructor <;> intro h <;> linarith

theorem rightCap_stationary_radii_ne_of_lt_half {a b : ℝ}
    (hb : b < 1 / 2) :
    b - a ≠ 1 - a - b := by
  intro h
  have hhalf := (rightCap_stationary_radii_eq_iff_half a b).mp h
  linarith

#print axioms canonicalPureGap_rightCap_full_radial_eq
#print axioms deriv_canonicalPureGap_rightCap_full_radial
#print axioms rightCap_stationary_radii_eq_iff_half
#print axioms rightCap_stationary_radii_ne_of_lt_half

end GeneralCK
