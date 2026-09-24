import GeneralCK.ProfileConvexity

namespace GeneralCK.Scalar
open Set

/-- An elementary logit inequality that controls the slope of `P`. -/
theorem logit_slope_bound {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 2) :
    2 * v * (1 - v) * Real.log 2 * J v ≤ 1 - 2 * v := by
  let g : ℝ → ℝ := fun u => 1 - 2 * u - 2 * u * (1 - u) * Real.log 2 * J u
  have hd : ∀ u ∈ Ioc (0 : ℝ) (1 / 2),
      HasDerivAt g (-2 * (1 - 2 * u) * Real.log 2 * J u) u := by
    intro u hu
    have hu1 : u < 1 := by linarith [hu.2]
    have h := (((hasDerivAt_id u).const_mul 2).const_sub 1).sub
      (((((hasDerivAt_id u).const_mul 2).mul
        ((hasDerivAt_id u).const_sub 1)).mul_const (Real.log 2)).mul
        (hasDerivAt_J hu.1 hu1))
    convert! h using 1
    dsimp
    field_simp [hu.1.ne', show 1 - u ≠ 0 by linarith, log_two_pos.ne']
    ring
  have hm : AntitoneOn g (Ioc 0 (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (1 / 2))
      (f' := fun u => -2 * (1 - 2 * u) * Real.log 2 * J u)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      have hu' := interior_subset hu
      have hj := J_nonneg hu'.1 hu'.2
      have hr : 0 ≤ 1 - 2 * u := by linarith [hu'.2]
      have hpos : 0 ≤ 2 * (1 - 2 * u) * Real.log 2 * J u := by positivity
      nlinarith
  have hh : g (1 / 2) = 0 := by norm_num [g, J]
  have h := hm ⟨hv, hv'⟩ ⟨by norm_num, le_rfl⟩ hv'
  rw [hh] at h
  dsimp [g] at h
  linarith

/-- The ordinary derivative is asserted only in the physical interior. -/
theorem hasDerivAt_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    HasDerivAt P
      (2 + (1 - 2 * entropyInverse (1 - I)) /
        (Real.log 2 * entropyInverse (1 - I) * (1 - entropyInverse (1 - I)) *
          J (entropyInverse (1 - I)))) I := by
  have hd := (hasDerivAt_eta (by linarith : 0 < 1 - I) (by linarith : 1 - I < 1)).comp I
    ((hasDerivAt_id I).const_sub 1)
  convert! hd using 1
  ring

theorem deriv_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) :
    deriv P I = 2 + (1 - 2 * entropyInverse (1 - I)) /
      (Real.log 2 * entropyInverse (1 - I) * (1 - entropyInverse (1 - I)) *
        J (entropyInverse (1 - I))) := (hasDerivAt_P hI hI').deriv

theorem four_le_deriv_P {I : ℝ} (hI : 0 < I) (hI' : I < 1) : 4 ≤ deriv P I := by
  have hv := entropyInverse_pos (show 0 < 1 - I by linarith) (show 1 - I ≤ 1 by linarith)
  have hv' := entropyInverse_lt_half (show 0 ≤ 1 - I by linarith) (show 1 - I < 1 by linarith)
  have hJ := J_pos hv hv'
  have hvc : 0 < 1 - entropyInverse (1 - I) := by linarith
  have hD : 0 < Real.log 2 * entropyInverse (1 - I) * (1 - entropyInverse (1 - I)) *
      J (entropyInverse (1 - I)) := by positivity
  have hbound := logit_slope_bound hv hv'.le
  rw [deriv_P hI hI']
  have hr : 2 ≤ (1 - 2 * entropyInverse (1 - I)) /
      (Real.log 2 * entropyInverse (1 - I) * (1 - entropyInverse (1 - I)) *
        J (entropyInverse (1 - I))) := (le_div_iff₀ hD).2 (by nlinarith)
  linarith

theorem P_continuousOn : ContinuousOn P (Ico 0 1) := by
  apply eta_continuousOn.comp (continuous_const.sub continuous_id).continuousOn
  intro I hI
  change 0 < 1 - I ∧ 1 - I ≤ 1
  constructor <;> linarith [hI.1, hI.2]

@[simp] theorem P_zero : P 0 = 0 := by simp [P]

/-- The slope lower bound extends to increments based at zero by continuity,
without making an assertion about a two-sided derivative at zero. -/
theorem P_sub_four_mul_monotone : MonotoneOn (fun I => P I - 4 * I) (Ico 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (f' := fun I => deriv P I - 4)
  · exact P_continuousOn.sub (continuous_const.mul continuous_id).continuousOn
  · intro I hI
    rw [interior_Ico] at hI
    have hd := (hasDerivAt_P hI.1 hI.2).sub ((hasDerivAt_id I).const_mul 4)
    rw [← deriv_P hI.1 hI.2] at hd
    convert! hd.hasDerivWithinAt using 1
    simp
  · intro I hI
    rw [interior_Ico] at hI
    linarith [four_le_deriv_P hI.1 hI.2]

theorem P_increment_lower {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) (hab : a ≤ b) :
    4 * (b - a) ≤ P b - P a := by
  have h := P_sub_four_mul_monotone ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans hab, hb⟩ hab
  linarith

theorem four_mul_le_P {I : ℝ} (hI : 0 ≤ I) (hI' : I < 1) : 4 * I ≤ P I := by
  simpa using P_increment_lower (a := 0) le_rfl hI' hI

end GeneralCK.Scalar
