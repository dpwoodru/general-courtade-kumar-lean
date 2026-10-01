import CKLaneA3X.FinalPos

/-!
# CKLaneA3X.Owners — direct chart slot `directC3` (Lane A3)

TM certificate with `Tq = 3/10` (order 24), positivity checked on the rectangle
`t = 1/2 - u ∈ [1/5, 3/10]`, `ρ ∈ [3/20, 1)` (`FinalPos.coef_pos_region`, `m11_pos_region`).
-/

set_option linter.unusedVariables false

namespace CKLaneA3X

open GeneralCK GeneralCK.Correction

theorem dom_of {t ρ : ℝ} (h0 : 0 < t) (h1 : t ≤ 3 / 10) (h2 : 0 < ρ) (h3 : ρ < 1) : Dom t ρ := by
  refine ⟨h0, ?_, h2, h3⟩
  have : ((Tq : ℚ) : ℝ) = 3 / 10 := by norm_num [Tq]
  rw [this]; exact h1

/-- actual ratio minors on `u ∈ [1/5, 3/10]`, `ρ ∈ [3/20, 1)` -/
theorem actualRatioMinors_c3 {u ρ : ℝ} (hu0 : 1 / 5 ≤ u) (hu1 : u ≤ 3 / 10) (hr0 : 3 / 20 ≤ ρ)
    (hr1 : ρ < 1) : ActualRatioMinorsPositive u ρ := by
  have ht0 : 0 < 1 / 2 - u := by linarith
  have ht1 : 1 / 2 - u ≤ 3 / 10 := by linarith
  have hd := dom_of ht0 ht1 (by linarith) hr1
  have hT0 : (((1 / 5 : ℚ)) : ℝ) ≤ 1 / 2 - u := by push_cast; linarith
  have hS0 : (((-7 / 20 : ℚ)) : ℝ) ≤ ρ - 1 / 2 := by push_cast; linarith
  have hc := coef_pos_region (1 / 2 - u) ρ hd hT0 hS0
  have hm := m11_pos_region (1 / 2 - u) ρ hd hT0 hS0
  have hk : 0 < Natural.kdet (1 / 2 - (1 / 2 - u)) (1 / 2 - (1 - ρ) * (1 / 2 - u)) := by
    rw [HighU.kdet_eq_gap_sq_mul_coefficient (dom_u_pos hd) (dom_u_lt_w hd) (dom_w_lt hd)]
    have hg : 0 < (1 / 2 - (1 - ρ) * (1 / 2 - u)) - (1 / 2 - (1 / 2 - u)) := sub_pos.mpr (dom_u_lt_w hd)
    positivity
  have e1 : 1 / 2 - (1 / 2 - u) = u := by ring
  have e2 : 1 / 2 - (1 - ρ) * (1 / 2 - u) = u + ρ * (1 / 2 - u) := by ring
  rw [e1, e2] at hm hk
  exact minors_of_pos (by linarith) (by linarith) (by linarith) hr1 hm hk

/-- `ChartOwners.directC3` -/
theorem directC3 : Complement.SignsOnBox (1 / 5) (3 / 10) (3 / 20) 1 := by
  intro u ρ _ _ _ hr' huB hrB
  exact Complement.ratioSigns_of_positive (actualRatioMinors_c3 huB.1 huB.2 hrB.1 hr')

end CKLaneA3X
