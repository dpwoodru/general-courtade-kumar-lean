/-
Lane N1 — FINAL instantiation of the `leftLower` field of
`CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff` (provider root P/genroot).

Case `b ≥ S - a` (double cap): the compiled external owner
`GeneralCK.canonicalDoubleCapEntropyEndpoints_of_joint_batches` (I-A closure in P/genroot) through
`canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints`.
Case `a + b < S` (cutoff edge): `CKLaneN1.Edge.leftEdge_retained` (kernel-checked box tree).
The case split is the one of `PositiveCutoffCapProbabilityOwners.toExceptEqual` (corpus source
`PureGapPositiveCutoffCapReduction.lean`, not compiled in the provider root).
-/
import CKLaneN1.EdgeFinal
import GeneralCK.PureGapDoubleCapBatchJointOwnerAdapter

set_option autoImplicit false

namespace CKLaneN1.Edge

open GeneralCK SmallMeanPhiCutoff

/-- The `leftLower` field of `CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff`. -/
theorem leftLower_certified :
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff f (entropyInverse e) ≤ 1 / 2 →
      0 ≤ canonicalPureGap (entropyInverse e) (capFiberLower retainedCutoff f (entropyInverse e))
        e f := by
  intro e f he hef hf hhalf
  have hie := entropyInverse_spec he.le (hef.le.trans hf)
  have hif := entropyInverse_spec (he.trans hef).le hf
  have ha : 0 < entropyInverse e := entropyInverse_pos he (hef.le.trans hf)
  have hab : entropyInverse e < entropyInverse f := entropyInverse_strictMonoOn
    ⟨he.le, hef.le.trans hf⟩ ⟨(he.trans hef).le, hf⟩ hef
  have hb : entropyInverse f ≤ 1 / 2 := hif.2.1
  by_cases hedge : retainedCutoff - entropyInverse e ≤ entropyInverse f
  · have hmax : capFiberLower retainedCutoff f (entropyInverse e) = entropyInverse f := by
      unfold capFiberLower
      exact max_eq_left hedge
    rw [hmax]
    exact canonicalPureGap_inverse_doubleCap_nonneg_of_scalar_endpoints
      canonicalDoubleCapEntropyEndpoints_of_joint_batches he hef hf
  · have hbEdge : entropyInverse f < retainedCutoff - entropyInverse e := lt_of_not_ge hedge
    have hmax : capFiberLower retainedCutoff f (entropyInverse e) =
        retainedCutoff - entropyInverse e := by
      unfold capFiberLower
      exact max_eq_right hbEdge.le
    have hhalf' : retainedCutoff - entropyInverse e ≤ 1 / 2 := by
      rw [hmax] at hhalf
      exact hhalf
    have hv := leftEdge_retained (entropyInverse e) (entropyInverse f) ha hab hb hbEdge hhalf'
    rw [hie.2.2, hif.2.2] at hv
    rw [hmax]
    exact hv

/-- Binding check: `leftLower_certified` is accepted in the `leftLower` slot of the structure
(elaborated against the field's own expected type). -/
example (o : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff) :
    CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff :=
  { o with leftLower := leftLower_certified }

end CKLaneN1.Edge
