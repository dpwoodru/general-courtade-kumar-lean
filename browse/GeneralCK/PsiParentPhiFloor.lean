import GeneralCK.PsiLowEntropyLeafReplay
import GeneralCK.RadialContact

/-! # The analytic all-bias parent lower bound

The entropy chord bounds its inverse by `E/2`. Comparing the radial
contact with that inverse gives the parent lower bound used by the five
checked high-bias leaves, with no remaining analytic hypothesis.
-/

namespace GeneralCK.PsiParentPhiFloor
open Set

theorem entropy_chord {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1 / 2) : 2 * v ≤ H v := by
  have h := Real.strictConcave_binEntropy.concaveOn.2
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show 0 ≤ 1 - 2 * v by linarith) (show 0 ≤ 2 * v by positivity)
    (show 1 - 2 * v + 2 * v = 1 by ring)
  simp only [smul_eq_mul, Real.binEntropy_zero, show Real.binEntropy (1 / 2 : ℝ) = Real.log 2 by simp,
    mul_zero, zero_add, show (2 * v) * (1 / 2) = v by ring] at h
  exact (le_div_iff₀ log_two_pos).mpr h

theorem phi_lower {q E : ℝ} (hq : 0 < q) (hE : 0 < E) (hEq : E < 1 - q) :
    (1 - q - E) * (Real.log ((2 - E) / E) / Real.log 2) ≤
      phi ((1 - q) / 2) E := by
  have hE1 : E < 1 := by linarith
  let v := entropyInverse E
  have hv : 0 < v := entropyInverse_pos hE hE1.le
  have hv1 : v ≤ 1 / 2 := (entropyInverse_spec hE.le hE1.le).2.1
  have hvE : H v = E := (entropyInverse_spec hE.le hE1.le).2.2
  have hvb : 2 * v ≤ E := by simpa only [hvE] using entropy_chord hv.le hv1
  have hvw : v ≤ radialContact q E := by
    apply (le_radialContact_iff hq hE hv.le hv1).mpr
    rw [hvE]
    nlinarith
  have hF : F q E ≤ q * J v := by
    rw [F, if_neg hq.ne']
    exact mul_le_mul_of_nonneg_left
      (J_antitone hv (radialContact_lt_half hq hE).le hvw) hq.le
  have hJ := J_antitone hv (show E / 2 ≤ 1 / 2 by linarith)
    (show v ≤ E / 2 by linarith)
  have hJ0 := J_nonneg hv hv1
  have hmul := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 1 - q - E by linarith)
  have hcoef := mul_nonneg (show 0 ≤ E - 2 * v by linarith) hJ0
  have heq : J (E / 2) = Real.log ((2 - E) / E) / Real.log 2 := by
    unfold J
    congr 2
    field_simp
  rw [heq] at hmul
  unfold phi
  rw [show |1 - 2 * ((1 - q) / 2)| = q by
    rw [show 1 - 2 * ((1 - q) / 2) = q by ring, abs_of_pos hq],
    eta_eq_profile hE.le hE1.le]
  change _ ≤ (1 - 2 * v) * J v - F q E
  nlinarith only [hF, hmul, hcoef]

theorem high_bias_parent_dominance {q E : ℝ} (hq : 2 / 5 ≤ q) (hq1 : q ≤ 15 / 16)
    (hE : 0 < E) (hEs : E ≤ 1 / 1000000) :
    psi ((1 - q) / 2) E + 1 / 10 ≤ phi ((1 - q) / 2) E :=
  (LowEntropyLeaf.psi_add_margin_le_lowEntropyA hq hq1 hE hEs).trans
    (phi_lower (by linarith) hE (by linarith))

end GeneralCK.PsiParentPhiFloor

#print axioms GeneralCK.PsiParentPhiFloor.phi_lower
#print axioms GeneralCK.PsiParentPhiFloor.high_bias_parent_dominance
