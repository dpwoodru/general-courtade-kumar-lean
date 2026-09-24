import GeneralCK.Certificates.E8TAxisRegularDyadicEvaluator
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.FullCertificate

/-! The zero-endpoint source evaluator specialized to the completed, kernel-checked
complex derivative certificate. No production Lipschitz premise remains. -/

namespace GeneralCK.Certificates.E8TAxisRegularUnconditionalSource
open Set Metric DyadicInterval E8TauInverseContraction
open E8TAxisRegularGermJet E8TAxisRegularDyadicEvaluator

theorem remainder_lipschitz :
    LipschitzOnWith (1 : NNReal) thetaTauRemainder (closedBall 0 tauRadius) := by
  exact E8ThetaTauAnalytic.thetaTauRemainder_lipschitz_of_deriv_bound
    (E8ThetaTauDerivativeFormula.final_derivative_bound_of_expr_bound
      Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound)

theorem regularJetBox_contains {p : ℕ} {box : DyadicInterval p} {y : ℝ}
    (hy : box.Contains y) (hy0 : 0 ≤ y) (hyUpper : y ≤ 4 / 25) :
    (regularJetBox box).Contains regularQJet y :=
  regularJetBox_sound remainder_lipschitz hy hy0 hyUpper

theorem regularComponentBox_contains {p : ℕ} {box : DyadicInterval p}
    {y : ℝ} (j : ℕ) (hj : j ≤ 5)
    (hy : box.Contains y) (hy0 : 0 ≤ y) (hyUpper : y ≤ 4 / 25) :
    (regularComponentBox j box).Contains
      (E8TAxisRegularSourceBounds.component regularQJet j y) :=
  regularComponentBox_sound remainder_lipschitz j hj hy hy0 hyUpper

#print axioms remainder_lipschitz
#print axioms regularJetBox_contains
#print axioms regularComponentBox_contains
end GeneralCK.Certificates.E8TAxisRegularUnconditionalSource
