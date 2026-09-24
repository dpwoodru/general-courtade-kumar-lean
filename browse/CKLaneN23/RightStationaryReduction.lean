import GeneralCK.PureGapCapAnalytic
import GeneralCK.SmallMeanPhiRetainedCutoff

/-!
# Lane N23 — `capFibers.rightStationary`: probability-coordinate target (CONDITIONAL adapter)

`RightStationaryProb S` is manuscript RA-stat (integrated review Thm 3.18(i), radial cap
`0 < b < c < a < 1/2`) in the lower-half probability coordinates of
`PositiveCutoffCapProbabilityOwners.rightStationary` (F-C source
`PureGapPositiveCutoffCapReduction.lean`, lines 31–34 and 137–154, not compiled in the F-C root).
`rightStationary_of_prob` reproduces that branch verbatim and lands in the exact field type of
`CanonicalPureGapCapFiberOwnersExceptEqual.rightStationary`. It is conditional on
`RightStationaryProb`; it is NOT a closure of the field.
-/

namespace CKLaneN23.RS

open GeneralCK

/-- RA-stat in probability coordinates at cutoff `S`. -/
def RightStationaryProb (S : ℝ) : Prop :=
  ∀ a x b : ℝ, 0 < a → a < x → x < b → b ≤ 1 / 2 → S < x + b →
    deriv (fun y => canonicalPureGap y b (H a) (H b)) x = 0 →
    0 ≤ canonicalPureGap x b (H a) (H b)

/-- The exact field type (printed by `AuditRS.lean`, line 13). -/
def RightStationaryField (S : ℝ) : Prop :=
  ∀ (e f a : ℝ), 0 < e → e < f → f ≤ 1 →
    capFiberLower S e (entropyInverse f) < a → a < entropyInverse f →
    deriv (fun x => canonicalPureGap x (entropyInverse f) e f) a = 0 →
    0 ≤ canonicalPureGap a (entropyInverse f) e f

/-- Verbatim port of the `rightStationary` branch of
`PositiveCutoffCapProbabilityOwners.toExceptEqual`. -/
theorem rightStationaryField_of_prob {S : ℝ} (h : RightStationaryProb S) :
    RightStationaryField S := by
  intro e f x he hef hf hx hxb hderiv
  let a := entropyInverse e
  let b := entropyInverse f
  have hie := entropyInverse_spec he.le (hef.le.trans hf)
  have hif := entropyInverse_spec (he.trans hef).le hf
  have ha : 0 < a := entropyInverse_pos he (hef.le.trans hf)
  have hax : a < x := (le_max_left a (S - b)).trans_lt (by
    simpa only [capFiberLower, a, b, hie.2.2] using hx)
  have hsum : S < x + b := by
    have hcut : S - b < x := (le_max_right a (S - b)).trans_lt (by
      simpa only [capFiberLower, a, b, hie.2.2] using hx)
    linarith
  have hv := h a x b ha hax (by simpa only [b] using hxb)
    hif.2.1 hsum (by
      simpa only [a, b, hie.2.2, hif.2.2] using hderiv)
  rw [hie.2.2, hif.2.2] at hv
  exact hv

/-- The field at the production cutoff, from RA-stat at the production cutoff. -/
theorem rightStationary_retained_of_prob
    (h : RightStationaryProb SmallMeanPhiCutoff.retainedCutoff) :
    RightStationaryField SmallMeanPhiCutoff.retainedCutoff :=
  rightStationaryField_of_prob h

/-- The field type is literally the structure field's type. -/
example (o : CanonicalPureGapCapFiberOwnersExceptEqual SmallMeanPhiCutoff.retainedCutoff) :
    RightStationaryField SmallMeanPhiCutoff.retainedCutoff :=
  o.rightStationary

end CKLaneN23.RS
