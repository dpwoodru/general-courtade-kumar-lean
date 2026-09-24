/-
Lane P — the `rightLower` field of `CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff`.

The lower endpoint of the right cap fiber is `max (entropyInverse e) (S − entropyInverse f)`.
* If it is `a = entropyInverse e`, the value is the double-cap value, owned by the scalar endpoint
  theorem `CanonicalDoubleCapEntropyEndpoints` (hypothesis `hdouble` here).
* Otherwise `a < S − b ≤ b < S = 1/10000`, and the right fiber is increasing on `[a, S − b]`
  (`rightFiber_mono`), so the value is at least the double-cap value.
This module is conditional on `hdouble`; `CKLaneP.RightLowerFinal` instantiates it with the
compiled external owner.
-/
import CKLaneP.RightFiber
import GeneralCK.PureGapCapAnalytic
import GeneralCK.SmallMeanPhiRetainedCutoff

set_option autoImplicit false

namespace CKLaneP

open GeneralCK Set SmallMeanPhiCutoff

theorem retainedCutoff_eq : retainedCutoff = 1 / 10000 := rfl

/-- `rightLower` from the double-cap scalar endpoints (conditional on `hdouble`). -/
theorem rightLower_of_doubleCap (hdouble : CanonicalDoubleCapEntropyEndpoints) :
    ∀ e f : ℝ, 0 < e → e < f → f ≤ 1 →
      capFiberLower retainedCutoff e (entropyInverse f) ≤ entropyInverse f →
      0 ≤ canonicalPureGap (capFiberLower retainedCutoff e (entropyInverse f))
        (entropyInverse f) e f := by
  intro e f he hef hf hle
  have hie := entropyInverse_spec he.le (hef.le.trans hf)
  have hif := entropyInverse_spec (he.trans hef).le hf
  have ha : 0 < entropyInverse e := entropyInverse_pos he (hef.le.trans hf)
  have hab : entropyInverse e < entropyInverse f :=
    entropyInverse_strictMonoOn ⟨he.le, hef.le.trans hf⟩ ⟨(he.trans hef).le, hf⟩ hef
  have hb : entropyInverse f ≤ 1 / 2 := hif.2.1
  have hHa : H (entropyInverse e) = e := hie.2.2
  have hHb : H (entropyInverse f) = f := hif.2.2
  have hdc := canonicalPureGap_doubleCap_nonneg_of_scalar_endpoints hdouble ha hab.le hb
  rw [hHa, hHb] at hdc
  by_cases hedge : retainedCutoff - entropyInverse f ≤ entropyInverse e
  · have hmax : capFiberLower retainedCutoff e (entropyInverse f) = entropyInverse e := by
      unfold capFiberLower
      exact max_eq_left hedge
    rw [hmax]
    exact hdc
  · have haEdge : entropyInverse e < retainedCutoff - entropyInverse f := lt_of_not_ge hedge
    have hmax : capFiberLower retainedCutoff e (entropyInverse f) =
        retainedCutoff - entropyInverse f := by
      unfold capFiberLower
      exact max_eq_right haEdge.le
    rw [hmax] at hle ⊢
    have hbS : entropyInverse f ≤ 1 / 10000 := by
      rw [retainedCutoff_eq] at hle haEdge
      linarith
    have hmono := rightFiber_mono ha haEdge.le hle hbS
    rw [hHa, hHb] at hmono
    linarith

end CKLaneP
