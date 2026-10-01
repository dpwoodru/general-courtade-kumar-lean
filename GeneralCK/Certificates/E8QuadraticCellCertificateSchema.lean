import GeneralCK.Certificates.E8QuadraticBallAcceptance
import GeneralCK.Certificates.E8LocalContactBall

/-! Production leaf schema using the sound squared-Euclidean output test. -/

namespace GeneralCK.Certificates.E8QuadraticCellCertificateSchema

open E8GaussianRatBall E8LocalContactBall E8RoundedDerivativeEvaluator
open E8CoupledTauCBox E8QuadraticBallAcceptance

def precision : ℕ := 2^40

structure CellCertificate where
  tauBall : RatBall
  contactCenter : GaussianRat
  contactBall : RatBall
  work : RoundedTauEval
  center_sq : (contactCenter.re : ℝ) ^ 2 + (contactCenter.im : ℝ) ^ 2 ≤
    (1/9 : ℝ)
  contact_eq : localContactBall tauBall contactCenter = contactBall
  work_eq : evalTau precision tauBall contactBall logTwoBall = work
  theta_ok : work.theta.ok = true
  jac_ok : work.jac.invOK = true
  accepted : acceptsUnitSq work.out = true

theorem CellCertificate.sound (cell : CellCertificate) {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ)) (hcell : cell.tauBall.Holds tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  have hc : cell.contactBall.Holds
      (Reflection.ComplexGlobalAnalytic.fixedPointOnDisc tau) := by
    rw [← cell.contact_eq]
    exact localContactBall_sound_sq htau hcell cell.center_sq
  have hthetaWork : (evalTau precision cell.tauBall cell.contactBall
      logTwoBall).theta.ok = true := by rw [cell.work_eq]; exact cell.theta_ok
  have htheta : (evalTheta precision cell.contactBall logTwoBall).ok = true := by
    simpa [evalTau] using hthetaWork
  have hjac : (evalTau precision cell.tauBall cell.contactBall
      logTwoBall).jac.invOK = true := by rw [cell.work_eq]; exact cell.jac_ok
  have hout := evalTau_out_sound (D := precision) (by norm_num [precision])
    htau hcell hc logTwoBall_holds htheta hjac
  apply acceptsUnitSq_sound (b := cell.work.out) cell.accepted
  rwa [← cell.work_eq]

def CoveredBy (cells : List CellCertificate) (tau : ℂ) : Prop :=
  ∃ cell ∈ cells, cell.tauBall.Holds tau

theorem sound_of_covered (cells : List CellCertificate) {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ)) (hcover : CoveredBy cells tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases hcover with ⟨cell, _, hcell⟩
  exact cell.sound htau hcell

end GeneralCK.Certificates.E8QuadraticCellCertificateSchema
