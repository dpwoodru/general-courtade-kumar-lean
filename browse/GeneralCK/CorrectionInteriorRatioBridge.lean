import GeneralCK.CorrectionHessianNatural

namespace GeneralCK.Correction.Natural

/-- A closed interval certificate may have `rho ≤ 1`; the actual entropy
Hessian bridge only evaluates interior points, for which `rho < 1` is supplied
separately by the ordered-triangle domain. -/
theorem ratio_point_interior {u rho : ℝ} (hhalf : 0 < 1/2-u)
    (hr : 0 < rho) (hr1 : rho < 1) :
    u < u+rho*(1/2-u) ∧ u+rho*(1/2-u) < 1/2 := by
  constructor
  · nlinarith [mul_pos hr hhalf]
  · nlinarith [mul_pos (sub_pos.mpr hr1) hhalf]

/-- Ratio-coordinate form of `kernel_eq_actual`. No strict upper bound is
required of a surrounding certificate box; only the evaluated point has to
satisfy `rho < 1`. -/
theorem kernel_eq_actual_ratio {u rho : ℝ} (hu : 0 < u) (hhalf : 0 < 1/2-u)
    (hr : 0 < rho) (hr1 : rho < 1) :
    m11 u (u+rho*(1/2-u)) = Mleft (H u) (H (u+rho*(1/2-u))) ∧
    kdet u (u+rho*(1/2-u)) = Kfactored (H u) (H (u+rho*(1/2-u))) := by
  obtain ⟨huw, hw⟩ := ratio_point_interior hhalf hr hr1
  exact kernel_eq_actual hu huw hw

#print axioms ratio_point_interior
#print axioms kernel_eq_actual_ratio

end GeneralCK.Correction.Natural
