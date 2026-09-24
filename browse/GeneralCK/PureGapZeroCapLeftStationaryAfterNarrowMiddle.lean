import GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddleCertified

/-! Exact residual stationary owner after the accepted narrow exclusion. -/

namespace GeneralCK

def LeftStationaryOutsideNarrowMiddleOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ ((1 / 8 : ℝ) ≤ entropyInverse e ∧
      entropyInverse e ≤ 129 / 1024 ∧
      129 / 1024 ≤ entropyInverse f ∧
      entropyInverse f ≤ 65 / 512 ∧
      1 / 4 ≤ c ∧ c ≤ 5 / 16) →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_of_outsideNarrowMiddle
    (h : LeftStationaryOutsideNarrowMiddleOwner) :
    ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
      entropyInverse f < c → c < 1 / 2 →
      deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
      0 ≤ canonicalPureGap (entropyInverse e) c e f := by
  intro e f c he hef hf hfc hc hstation
  by_cases hbox : (1 / 8 : ℝ) ≤ entropyInverse e ∧
      entropyInverse e ≤ 129 / 1024 ∧
      129 / 1024 ≤ entropyInverse f ∧
      entropyInverse f ≤ 65 / 512 ∧
      1 / 4 ≤ c ∧ c ≤ 5 / 16
  · have he1 : e ≤ 1 := (hef.trans hf).le
    have hf0 : 0 ≤ f := (he.trans hef).le
    have hie := entropyInverse_spec he.le he1
    have hif := entropyInverse_spec hf0 hf.le
    have hnot := ZeroCapLeftStationaryNarrowMiddleCertified.no_left_stationary_in_narrow_middle
      hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2.1 hbox.2.2.2.2.1 hbox.2.2.2.2.2
    rw [hie.2.2, hif.2.2] at hnot
    exact False.elim (hnot hstation)
  · exact h e f c he hef hf hfc hc hstation hbox

#print axioms leftStationary_of_outsideNarrowMiddle

end GeneralCK
