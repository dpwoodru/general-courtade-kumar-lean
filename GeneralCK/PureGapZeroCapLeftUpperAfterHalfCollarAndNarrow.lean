import GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollar
import GeneralCK.PureGapZeroCapLeftUpperNarrowRectangle

/-! The exact left-upper remainder after two unconditional certified regions. -/

namespace GeneralCK

def LeftUpperOutsideHalfCollarAndNarrowOwner : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 / 2 → a < 31 / 64 →
    ¬ ((1 / 8 : ℝ) ≤ a ∧ a ≤ 129 / 1024 ∧
      129 / 1024 ≤ b ∧ b ≤ 65 / 512) →
    0 ≤ canonicalPureGap a (1 / 2) (H a) (H b)

theorem leftUpper_outsideHalfCollar_of_outsideNarrow
    (h : LeftUpperOutsideHalfCollarAndNarrowOwner) :
    LeftUpperOutsideHalfCollarOwner := by
  intro a b ha hab hb ha31
  by_cases hrect : (1 / 8 : ℝ) ≤ a ∧ a ≤ 129 / 1024 ∧
      129 / 1024 ≤ b ∧ b ≤ 65 / 512
  · exact ZeroCapLeftUpperNarrow.leftUpper_on_narrow_rectangle
      hrect.1 hrect.2.1 hrect.2.2.1 hrect.2.2.2 hab
  · exact h a b ha hab hb ha31 hrect

theorem zeroCap_leftUpper_of_outsideHalfCollarAndNarrow
    (h : LeftUpperOutsideHalfCollarAndNarrowOwner) :
    ∀ e f, 0 < e → e < f → f < 1 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f :=
  zeroCap_leftUpper_of_outsideHalfCollar
    (leftUpper_outsideHalfCollar_of_outsideNarrow h)

#print axioms leftUpper_outsideHalfCollar_of_outsideNarrow
#print axioms zeroCap_leftUpper_of_outsideHalfCollarAndNarrow

end GeneralCK
