import GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600Actual

/-!
Exact remaining left-upper probability chamber after the accepted half-collar.
The outside sign remains an explicit analytic/certificate premise.
-/

namespace GeneralCK

def LeftUpperOutsideHalfCollarOwner : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 / 2 → a < 31 / 64 →
    0 ≤ canonicalPureGap a (1 / 2) (H a) (H b)

theorem leftUpper_probability_of_outsideHalfCollar
    (h : LeftUpperOutsideHalfCollarOwner) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    0 ≤ canonicalPureGap a (1 / 2) (H a) (H b) := by
  by_cases ha31 : (31 / 64 : ℝ) ≤ a
  · let z : ℝ := 1 / 2 - a
    let lambda : ℝ := (1 / 2 - b) / z
    have hz : 0 < z := by dsimp [z]; linarith
    have hzmax : z ≤ 1 / 64 := by dsimp [z]; linarith
    have hw : 0 < 1 / 2 - b := by linarith
    have hwz : 1 / 2 - b < z := by dsimp [z]; linarith
    have hlambda : 0 < lambda := div_pos hw hz
    have hlambda1 : lambda < 1 := (div_lt_one hz).2 hwz
    have hza : 1 / 2 - z = a := by dsimp [z]; ring
    have hzb : 1 / 2 - lambda * z = b := by
      dsimp [lambda]
      rw [div_mul_cancel₀ _ hz.ne']
      ring
    have hp := leftUpper_halfCollar_positive_unconditional
      hz hzmax hlambda hlambda1
    rw [hza, hzb] at hp
    exact hp.le
  · exact h a b ha hab hb (lt_of_not_ge ha31)

theorem zeroCap_leftUpper_of_outsideHalfCollar
    (h : LeftUpperOutsideHalfCollarOwner) :
    ∀ e f, 0 < e → e < f → f < 1 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f := by
  have hsign : ZeroCapLeftUpperRadialSign := by
    intro a b ha hab hb
    have hp := leftUpper_probability_of_outsideHalfCollar h ha hab hb
    rw [canonicalPureGap_leftUpper_radial_eq ha hab hb] at hp
    linarith
  exact zeroCap_leftUpper_of_radialSign hsign

#print axioms leftUpper_probability_of_outsideHalfCollar
#print axioms zeroCap_leftUpper_of_outsideHalfCollar

end GeneralCK
