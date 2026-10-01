import GeneralCK.PsiExtendedEntropyCurvature
import GeneralCK.PsiSignedSplit

/-!
# Retaining and coupling the two child entropies

The signed split correction is derived from the actual two radialPhi values.
In particular, the average entropy is not assumed to lie below either child's
feasible cap. This is the analytic step lost by the refuted mean-only shortcut.
-/

namespace GeneralCK.PsiChildEntropyCoupling
open PsiExtendedEntropyCurvature PsiSignedSplit

noncomputable def childAverage (d q E t : ℝ) : ℝ :=
  (radialPhi (d + q) (E * (1 + t)) + radialPhi (d - q) (E * (1 - t))) / 2

noncomputable def slopeDifference (d q E : ℝ) : ℝ :=
  deriv (radialPhi (d + q)) E - deriv (radialPhi (d - q)) E

/-- Exact signed lower bound for the average of the two child phi values. -/
theorem child_average_lower {d q E t : ℝ} (hq : 0 ≤ q) (hqd : q ≤ d)
    (hE : 0 < E) (hEi : E ≤ 11 / 200) (ht : |t| < 1) :
    (radialPhi (d + q) E + radialPhi (d - q) E) / 2 +
      E * t * slopeDifference d q E / 2 +
      compensation d * barrier t / 2 +
      (13 * q / 6) * (tilt t - t) ≤ childAverage d q E t := by
  have hti := abs_lt.mp ht
  have hep : 0 < E * (1 + t) := mul_pos hE (by linarith)
  have hem : 0 < E * (1 - t) := mul_pos hE (by linarith)
  have hEp : E * (1 + t) ≤ 11 / 100 := by
    nlinarith [mul_pos hE (show 0 < 1 - t by linarith)]
  have hEm : E * (1 - t) ≤ 11 / 100 := by
    nlinarith [mul_pos hE (show 0 < 1 + t by linarith)]
  have hp := radialPhi_tangent_lower (r := d + q) (by linarith)
    hE (by linarith) hep hEp
  have hm := radialPhi_tangent_lower (r := d - q) (by linarith)
    hE (by linarith) hem hEm
  have hpr : (E * (1 + t) - E) / E = t := by field_simp; ring
  have hmr : (E * (1 - t) - E) / E = -t := by field_simp; ring
  have hpl : E * (1 + t) / E = 1 + t := by field_simp
  have hml : E * (1 - t) / E = 1 - t := by field_simp
  rw [hpr, hpl] at hp
  rw [hmr, hml] at hm
  unfold childAverage slopeDifference compensation barrier tilt at *
  rw [log_one_sub_sq ht]
  linear_combination hp / 2 + hm / 2

noncomputable def endpointCoefficient (d : ℝ) : ℝ :=
  (1 + d) / (2 * Real.log 2) - 13 * d / 12

noncomputable def radialLoss (d q E : ℝ) : ℝ :=
  (F (d + q) E + F (d - q) E) / 2 - F d E

/-- The remaining child comparison separates into parent gain, radial loss,
and one explicitly signed split correction. `C` is an entropy increment. -/
theorem retained_child_decomposition {d q E t C : ℝ} (hq : 0 ≤ q) (hqd : q ≤ d)
    (hE : 0 < E) (hEi : E ≤ 11 / 200) (ht : |t| < 1) :
    eta E - eta (E + C) - radialLoss d q E +
      endpointCoefficient d * barrier t + E * t * slopeDifference d q E / 2 +
      (13 * q / 6) * (tilt t - t) ≤
      F d E + d / (2 * Real.log 2) * barrier t -
        (eta (E + C) - childAverage d q E t) := by
  have h := child_average_lower hq hqd hE hEi ht
  unfold endpointCoefficient radialLoss compensation radialPhi at *
  linear_combination h

end GeneralCK.PsiChildEntropyCoupling

#print axioms GeneralCK.PsiChildEntropyCoupling.child_average_lower
#print axioms GeneralCK.PsiChildEntropyCoupling.retained_child_decomposition
