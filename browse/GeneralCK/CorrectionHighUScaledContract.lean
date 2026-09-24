import GeneralCK.CorrectionFamilyAssembly
import GeneralCK.CorrectionInteriorRatioBridge

/-!
# Scaled contract for the correction high-u boundary

For `19/50 < u < 1/2`, write `t = 1/2-u` and
`w = 1/2-(1-rho)t`. The natural left minor and cleared determinant
become very small near `t=0` and `rho=0`. The scaled inequalities below
are a certificate target, not an assertion that certificates exist.
-/

namespace GeneralCK.Correction.HighU

def ScaledHighUOwner : Prop :=
  ∀ t rho : ℝ, 0 < t → t < 3 / 25 → 0 < rho → rho < 1 →
    0 < Natural.m11 (1 / 2 - t) (1 / 2 - (1 - rho) * t) / t ^ 2 ∧
    0 < Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t) /
      (rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2))

def ActualHighUOwner : Prop :=
  ∀ u rho : ℝ, 19 / 50 < u → u < 1 / 2 →
    0 < rho → rho < 1 → ActualRatioMinorsPositive u rho

/-- A complete scaled high-u certificate would imply the actual Hessian
minor signs on that open coordinate region. This theorem is conditional. -/
theorem actualHighU_of_scaledOwner (h : ScaledHighUOwner) :
    ActualHighUOwner := by
  intro u rho hu huhalf hr hr1
  let t := 1 / 2 - u
  let w := u + rho * (1 / 2 - u)
  have ht : 0 < t := by dsimp [t]; linarith
  have htu : t < 3 / 25 := by dsimp [t]; linarith
  obtain ⟨hm, hk⟩ := h t rho ht htu hr hr1
  have htd : 0 < t ^ 2 := pow_pos ht _
  have hkd : 0 < rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2) := by positivity
  have hm' := mul_pos hm htd
  have hk' := mul_pos hk hkd
  rw [div_mul_cancel₀ _ htd.ne'] at hm'
  rw [div_mul_cancel₀ _ hkd.ne'] at hk'
  have hcoordu : 1 / 2 - t = u := by dsimp [t]; ring
  have hcoordw : 1 / 2 - (1 - rho) * t = w := by dsimp [t, w]; ring
  rw [hcoordu, hcoordw] at hm' hk'
  have hu0 : 0 < u := by linarith
  obtain ⟨huw, hw⟩ := Natural.ratio_point_interior (sub_pos.mpr huhalf) hr hr1
  have huw' : u < w := by simpa only [w] using huw
  have hw' : w < 1 / 2 := by simpa only [w] using hw
  have heq := Natural.kernel_eq_actual_ratio hu0 (sub_pos.mpr huhalf) hr hr1
  have hw0 : 0 < H w := H_pos (hu0.trans huw') (by linarith [hw'])
  have hw1 : H w < 1 := by
    have hs := H_strictMonoOn
      ⟨(hu0.trans huw').le, hw'.le⟩
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2)) hw'
    simpa only [H_half] using hs
  change ActualRatioMinorsPositive u rho
  unfold ActualRatioMinorsPositive
  dsimp [w] at hm' hk' ⊢
  refine ⟨heq.1 ▸ hm', ?_⟩
  exact (Mdet_pos_iff_Kfactored_pos hw0 hw1).2 (heq.2 ▸ hk')

#print axioms actualHighU_of_scaledOwner

end GeneralCK.Correction.HighU
