/-
Lane N4b — the left-upper owner proposition from the certified cover (F-C consumer root).

`leftUpperOwner : GeneralCK.LeftUpperOutsideWideHalfCollarAndNarrowOwner` (unconditional: the
cover `root_good` is the conjunction of 1131 kernel-checked cells + the analytic origin lemma).
`leftUpper_lt_one`: the `f < 1` part of the `leftUpper` field (corpus reduction
`zeroCap_leftUpper_of_outsideWideHalfCollarAndNarrow`).
-/
import CKLaneN4.LU.Cover
import CKLaneN4.LU.OwnerBridge

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK

theorem ATOP_ge : (5 : ℝ) / 11 ≤ (ATOP : ℝ) / 2 ^ 64 := by
  unfold ATOP; norm_num

theorem leftUpperOwner : LeftUpperOutsideWideHalfCollarAndNarrowOwner :=
  owner_of_box ATOP_ge root_good

theorem leftUpper_lt_one : ∀ e f : ℝ, 0 < e → e < f → f < 1 →
    0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f :=
  zeroCap_leftUpper_of_outsideWideHalfCollarAndNarrow leftUpperOwner

end CKLaneN4.LU
