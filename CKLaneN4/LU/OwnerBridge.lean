/-
Lane N4b — from the certified chart box to the corpus owner proposition.

`cpg_eq_gexpr`: on `0 < a < b < 1/2`, `canonicalPureGap a (1/2) (H a) (H b) = Gexpr a b`
(corpus `canonicalPureGap_leftUpper_radial_eq` + `eta (H b) = (1 - 2b) J b`).
`owner_of_box`: a certified root box `[0, A] × [0, 1]` with `A/2^64 ≥ 5/11` yields
`GeneralCK.LeftUpperOutsideWideHalfCollarAndNarrowOwner`.
-/
import CKLaneN4.LU.Tree
import GeneralCK.PureGapZeroCapLeftUpperWideHalfCollar

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK

theorem eta_H_eq_kfun {b : ℝ} (hb : 0 < b) (hb2 : b ≤ 1 / 2) : eta (H b) = kfun b := by
  rw [eta_eq_profile (H_nonneg hb.le (by linarith)) (H_le_one b), entropyInverse_H_lower hb.le hb2]
  rfl

theorem cpg_eq_gexpr {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    canonicalPureGap a (1 / 2) (H a) (H b) = Gexpr a b := by
  rw [canonicalPureGap_leftUpper_radial_eq ha hab hb, eta_H_eq_kfun (ha.trans hab) hb.le]
  unfold Gexpr Cfun Vfun hAvg
  ring

theorem owner_of_box {A : ℕ} (hA : (5 : ℝ) / 11 ≤ (A : ℝ) / 2 ^ 64)
    (hroot : BoxGood 0 A 0 18446744073709551616) :
    LeftUpperOutsideWideHalfCollarAndNarrowOwner := by
  intro a b ha hab hb ha511 _
  rw [cpg_eq_gexpr ha hab hb]
  have h12 : 0 < 1 / 2 - a := by linarith
  have ht : 0 < (b - a) / (1 / 2 - a) := div_pos (by linarith) h12
  have ht1 : (b - a) / (1 / 2 - a) ≤ 1 := by rw [div_le_one h12]; linarith
  have hbt : bAt a ((b - a) / (1 / 2 - a)) = b := by
    unfold bAt; rw [div_mul_cancel₀ _ h12.ne']; ring
  rw [← hbt]
  have e0 : ((0 : ℕ) : ℝ) / 2 ^ 64 = 0 := by simp
  have e1 : ((18446744073709551616 : ℕ) : ℝ) / 2 ^ 64 = 1 := by norm_num
  refine hroot a _ ?_ ?_ ?_ ?_ ha ht
  · rw [e0]; exact ha.le
  · linarith
  · rw [e0]; exact ht.le
  · rw [e1]; exact ht1

end CKLaneN4.LU
