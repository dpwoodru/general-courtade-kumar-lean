import E8RatioMonotonicity
import GeneralCK.Certificates.E8HistoricalTailIdentity

/-! Ratio-form adapter to the historical scalar, without expanded polynomials. -/

namespace GeneralCK.E8RatioMonotonicity

open Set Filter
open Certificates.E8TAxisStableScalar
open Certificates.E8TAxisStableJet5
open Certificates.E8HistoricalLogConvexityBridge
open Certificates.E8InverseJet5Bridge

theorem stable_xPrime_pos {a : ℝ} (ha : 0 < a) : 0 < xJet.d1 a := by
  rw [xJet_d1_eq_historicalXPrime a ha]
  exact historicalXPrime_pos a ha

/-- Positivity holds on the full positive stable axis, including `a < 1`. -/
theorem stable_yPrime_pos {a : ℝ} (ha : 0 < a) : 0 < yJet.d1 a := by
  have htheta := (hasDerivAt_e8Theta (X_pos ha)).differentiableAt.hasDerivAt
  have hcomp := htheta.comp a (hasDerivAt_X a ha)
  have heq : Y =ᶠ[nhds a] (e8Theta ∘ X) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact (e8Theta_X hb).symm
  have hY := hcomp.congr_of_eventuallyEq heq
  have hj : HasDerivAt Y (yJet.d1 a) a := by
    convert (yJet_soundAt ha).1 using 1
    funext b
    exact (yJet_d0 b).symm
  have hid := hj.unique hY
  rw [hid]
  exact mul_pos (deriv_e8Theta_pos (X_pos ha)) (historicalXPrime_pos a ha)

/-- The canonical numerator is a positive ratio times the historical scalar. -/
theorem stable_numerator_eq_ratio_mul_L {a : ℝ} (ha : 0 < a) :
    e8LogDerivativeJetNumerator (Y a) =
      (xJet.d1 a ^ 2 / yJet.d1 a ^ 4) * stableL a := by
  have hx := (stable_xPrime_pos ha).ne'
  have hy := (stable_yPrime_pos ha).ne'
  rw [canonical_numerator_eq_cleared_div ha hy,
    stableLCleared_eq_stableL_mul hx hy]
  field_simp
  <;> ring

theorem stable_numerator_nonneg_iff_L_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ e8LogDerivativeJetNumerator (Y a) ↔ 0 ≤ stableL a := by
  rw [stable_numerator_eq_ratio_mul_L ha]
  exact mul_nonneg_iff_of_pos_left
    (div_pos (pow_pos (stable_xPrime_pos ha) 2) (pow_pos (stable_yPrime_pos ha) 4))

/-- `g'(X a)` as one ratio of the historical logarithmic derivative. -/
theorem ratio_X_eq {a : ℝ} (ha : 0 < a) :
    ratio (X a) = -stableE a / yJet.d1 a := by
  have hx := (stable_xPrime_pos ha).ne'
  have hy := (stable_yPrime_pos ha).ne'
  have ht := (deriv_e8Theta_pos (e8Q_pos (Y_mem_e8SlopeRange ha))).ne'
  rcases inverseJet_components ha hy with ⟨_, h1, h2, _, _, _⟩
  have hr : ratio (e8Q (Y a)) =
      (e8QJet5 e8ThetaCanonicalJet5).d2 (Y a) /
        (e8QJet5 e8ThetaCanonicalJet5).d1 (Y a) := by
    simp only [ratio, e8QJet5, e8ThetaCanonicalJet5]
    field_simp
    <;> ring
  rw [e8Q_Y ha, ← h1, ← h2] at hr
  rw [hr]
  simp only [inverseJet, Certificates.E8TAxisReparamJet5.qdata5, stableE]
  field_simp
  <;> ring

/-- Derivative of the exact ratio after the stable change of variable.
Its denominator is unconditionally positive; the sole sign target is `L`. -/
theorem hasDerivAt_ratio_X {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b => ratio (X b)) (stableL a / yJet.d1 a) a := by
  have hx := (stable_xPrime_pos ha).ne'
  have hy := (stable_yPrime_pos ha).ne'
  have hd := (hasDerivAt_stableE a ha hx hy).neg.div (yJet_soundAt ha).2.1 hy
  have hi := hd.congr_deriv (show _ = stableL a / yJet.d1 a from by
    simp only [Pi.neg_apply, stableL, stableE, stableX0]
    field_simp
    <;> ring)
  have heq : (fun b => ratio (X b)) =ᶠ[nhds a]
      (fun b => -stableE b / yJet.d1 b) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact ratio_X_eq hb
  have hj := hi.congr_of_eventuallyEq heq
  rw [hasDerivAt_iff_isLittleO] at hj ⊢
  simpa only [smul_eq_mul] using hj

theorem ratio_monotone_iff_stableL_nonneg :
    MonotoneOn ratio (Ioi 0) ↔ ∀ a : ℝ, 0 < a → 0 ≤ stableL a := by
  rw [← stable_numerator_nonnegative_iff_ratio_monotone]
  exact forall_congr' (fun a => forall_congr' (fun ha =>
    stable_numerator_nonneg_iff_L_nonneg ha))

/-- Only the scalar sign is open: both nonzero derivative fields are checked. -/
theorem tailCertificate_of_L_nonnegative {cut : ℝ} (hcut : 0 < cut)
    (hL : ∀ a : ℝ, cut ≤ a → 0 ≤ stableL a) : TailCertificate cut where
  xPrime_ne := fun a ha => (stable_xPrime_pos (hcut.trans_le ha)).ne'
  yPrime_ne := fun a ha => (stable_yPrime_pos (hcut.trans_le ha)).ne'
  L_nonnegative := hL

theorem largeSStructure_of_stableL_nonnegative
    (hL : ∀ a : ℝ, 0 < a → 0 ≤ stableL a) : E8LargeSStructure :=
  largeSStructure_of_ratio_monotone (ratio_monotone_iff_stableL_nonneg.mpr hL)

#print axioms stable_xPrime_pos
#print axioms stable_yPrime_pos
#print axioms stable_numerator_eq_ratio_mul_L
#print axioms stable_numerator_nonneg_iff_L_nonneg
#print axioms ratio_X_eq
#print axioms hasDerivAt_ratio_X
#print axioms ratio_monotone_iff_stableL_nonneg
#print axioms tailCertificate_of_L_nonnegative
#print axioms largeSStructure_of_stableL_nonnegative

end GeneralCK.E8RatioMonotonicity
