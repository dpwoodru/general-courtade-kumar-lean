import GeneralCK.Certificates.E8ThetaTauAnalytic

/-!
# Derivative handoff for the final E8 quantitative inverse bound

This removes the derivative of the implicit contact branch.  The only
derivative left in the displayed expression is that of the explicit
elementary function `thetaParam`, the target for a complex interval checker.
-/

namespace GeneralCK.Certificates.E8ThetaTauDerivativeFormula

open E8AnalyticGerm
open Reflection.ComplexEntropy
open Reflection.ComplexGlobalAnalytic
open E8TauInverseContraction
open E8ThetaTauAnalytic

noncomputable def thetaTauDerivExpr (tau : ℂ) : ℂ :=
  let c := fixedPointOnDisc tau
  deriv thetaParam c *
    (entropyExt c / (1 - tau * entropyDeriv c))

theorem hasDerivAt_thetaOfTau_expr {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    HasDerivAt thetaOfTau (thetaTauDerivExpr tau) tau := by
  have htau' : ‖tau‖ < (7 / 10 : ℝ) := htau.trans_lt (by norm_num)
  have hc := norm_fixedPointOnDisc_le htau
  have houter := (analyticAt_thetaParam_on_disc hc).differentiableAt.hasDerivAt
  have hinner := hasDerivAt_fixedPointOnDisc htau'
  change HasDerivAt (thetaParam ∘ fixedPointOnDisc) _ tau
  simpa only [thetaTauDerivExpr] using houter.comp tau hinner

theorem deriv_thetaTauRemainder_eq {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    deriv thetaTauRemainder tau = thetaTauDerivExpr tau - 4 := by
  have htheta := hasDerivAt_thetaOfTau_expr htau
  have hlinear : HasDerivAt (fun z : ℂ => 4 * z) 4 tau := by
    simpa using (hasDerivAt_id (𝕜 := ℂ) tau).const_mul 4
  have h := htheta.sub hlinear
  change deriv (thetaOfTau - fun z : ℂ => 4 * z) tau = _
  exact h.deriv

theorem final_derivative_bound_of_expr_bound
    (hExpr : ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
      ‖thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ)) :
    ∀ tau : ℂ, ‖tau‖ ≤ (2 / 5 : ℝ) →
      ‖deriv thetaTauRemainder tau‖ ≤ (1 : ℝ) := by
  intro tau htau
  rw [deriv_thetaTauRemainder_eq htau]
  exact hExpr tau htau

end GeneralCK.Certificates.E8ThetaTauDerivativeFormula
