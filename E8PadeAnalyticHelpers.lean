import E8CompactQuadraticSign

namespace GeneralCK.E8RatioMonotonicity

open Set Filter
open Certificates.E8TAxisStableScalar

noncomputable def padeLogGap (u : ℝ) : ℝ :=
  u * (2 + u) / (2 * (1 + u)) - Real.log (1 + u)

theorem hasDerivAt_padeLogGap {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt padeLogGap (u ^ 2 / (2 * (1 + u) ^ 2)) u := by
  have h1 : 1 + u ≠ 0 := by linarith
  have h2 : 2 * (1 + u) ≠ 0 := by positivity
  have hi := hasDerivAt_id u
  have hn := hi.mul ((hasDerivAt_const u 2).add hi)
  have hd := (hasDerivAt_const u 2).mul ((hasDerivAt_const u 1).add hi)
  have hl := ((hasDerivAt_const u 1).add hi).log h1
  have hf := (hn.div hd h2).sub hl
  convert! hf using 1
  simp only [Pi.mul_apply, Pi.add_apply, id_eq]
  field_simp [h1]
  ring

/-- The rational upper bound for the logarithm used by the Padé tail. -/
theorem log_one_add_le_pade {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u * (2 + u) / (2 * (1 + u)) := by
  have hm : MonotoneOn padeLogGap (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      exact (hasDerivAt_padeLogGap hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_padeLogGap (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hasDerivAt_padeLogGap (interior_subset hx)).deriv]
      positivity
  have hh := hm (show (0 : ℝ) ∈ Ici 0 by simp) hu hu
  simpa [padeLogGap] using hh

theorem twenty_le_exp_three : (20 : ℝ) ≤ Real.exp 3 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  linarith

theorem z_le_one_twentieth_of_three_halves {a : ℝ} (ha : 3 / 2 ≤ a) :
    z a ≤ 1 / 20 := by
  have hexp : (20 : ℝ) ≤ Real.exp (2 * a) :=
    twenty_le_exp_three.trans (Real.exp_le_exp.mpr (by linarith))
  have hid : z a * Real.exp (2 * a) = 1 := by
    rw [z, ← Real.exp_add]
    norm_num
  have hh := mul_le_mul_of_nonneg_left hexp (z_pos a).le
  rw [hid] at hh
  linarith

#print axioms log_one_add_le_pade
#print axioms twenty_le_exp_three
#print axioms z_le_one_twentieth_of_three_halves

end GeneralCK.E8RatioMonotonicity
