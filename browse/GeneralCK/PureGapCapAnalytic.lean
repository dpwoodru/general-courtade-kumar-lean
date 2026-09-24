import GeneralCK.PureGapCapFiberOwner
import GeneralCK.PureGapHalfMeanAnalytic

/-! The equal-mean cap endpoint is already owned by correction convexity.
The other five fiber obligations are retained explicitly. -/

namespace GeneralCK
open Set

theorem cap_rightUpper_nonneg_of_correction
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2)
    {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f ≤ 1) :
    0 ≤ canonicalPureGap (entropyInverse f) (entropyInverse f) e f := by
  have hf0 : 0 < f := he.trans hef
  have hm := entropyInverse_spec hf0.le hf
  have hmpos : 0 < entropyInverse f := by
    have hne : entropyInverse f ≠ 0 := by
      intro hz
      have hh := hm.2.2
      rw [hz, H_zero] at hh
      linarith
    exact lt_of_le_of_ne hm.1 (Ne.symm hne)
  rw [← pureGap_eq_canonicalPureGap le_rfl hm.2.1]
  apply pureGap_equal_mean_nonneg_of_convex
    (Correction.convexOn_entropyCorrection_square hleft hdet) hmpos
    (hm.2.1.trans_lt (by norm_num))
  · exact ⟨he, by rw [hm.2.2]; exact hef.le⟩
  · exact ⟨hf0, hm.2.2.ge⟩

/-- The scalar fiber data after consuming its equal-mean endpoint. -/
structure CanonicalPureGapCapFiberOwnersExceptEqual (S : ℝ) : Prop where
  leftLower : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower S f (entropyInverse e) ≤ 1 / 2 →
    0 ≤ canonicalPureGap (entropyInverse e) (capFiberLower S f (entropyInverse e)) e f
  leftUpper : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower S f (entropyInverse e) ≤ 1 / 2 →
    0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f
  leftStationary : ∀ e f c, 0 < e → e < f → f ≤ 1 →
    capFiberLower S f (entropyInverse e) < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    0 ≤ canonicalPureGap (entropyInverse e) c e f
  rightLower : ∀ e f, 0 < e → e < f → f ≤ 1 →
    capFiberLower S e (entropyInverse f) ≤ entropyInverse f →
    0 ≤ canonicalPureGap (capFiberLower S e (entropyInverse f)) (entropyInverse f) e f
  rightStationary : ∀ e f a, 0 < e → e < f → f ≤ 1 →
    capFiberLower S e (entropyInverse f) < a → a < entropyInverse f →
    deriv (fun x => canonicalPureGap x (entropyInverse f) e f) a = 0 →
    0 ≤ canonicalPureGap a (entropyInverse f) e f

theorem CanonicalPureGapCapFiberOwnersExceptEqual.toOwners {S : ℝ}
    (owners : CanonicalPureGapCapFiberOwnersExceptEqual S)
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2) :
    CanonicalPureGapCapFiberOwners S where
  leftLower := owners.leftLower
  leftUpper := owners.leftUpper
  leftStationary := owners.leftStationary
  rightLower := owners.rightLower
  rightUpper := by
    intro e f he hef hf _
    exact cap_rightUpper_nonneg_of_correction hleft hdet he hef hf
  rightStationary := owners.rightStationary

/-- An optional zero cutoff makes the small region empty. Choosing it also
enlarges the cap certificate domains; it is not an import of the retained
positive-cutoff archives. -/
theorem canonicalPureGap_small_zero :
    ∀ e f p, 0 < e → 0 < f → e < f → p ∈ canonicalMeanSet e f →
      p.1 + p.2 < (0 : ℝ) → 0 ≤ canonicalPureGap p.1 p.2 e f := by
  intro e f p _ _ _ hp hsum
  have ha : 0 ≤ p.1 := hp.1
  have hc : p.1 ≤ p.2 := hp.2.1
  linarith

theorem strictSeamMinimizerExclusion_zero : StrictSeamMinimizerExclusion 0 := by
  intro a c e f _ _ _ hp hsum hac _ _ _ _ _
  have ha : 0 ≤ a := hp.1.1
  linarith

#print axioms cap_rightUpper_nonneg_of_correction
#print axioms CanonicalPureGapCapFiberOwnersExceptEqual.toOwners
#print axioms canonicalPureGap_small_zero
#print axioms strictSeamMinimizerExclusion_zero

end GeneralCK
