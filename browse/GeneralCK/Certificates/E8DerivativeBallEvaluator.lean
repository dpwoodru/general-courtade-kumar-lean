import GeneralCK.Certificates.E8CoupledTauCBox

/-! Executable rational-ball evaluation of the E8 tau derivative. -/

namespace GeneralCK.Certificates.E8DerivativeBallEvaluator

open E8GaussianRatBall E8ComplexLogBoxChecker E8CoupledTauCBox
open E8ThetaParamDerivativeExplicit E8ThetaTauDerivativeFormula
open E8AnalyticGerm
open Reflection.ComplexEntropy Reflection.ComplexGlobalAnalytic
open E8ThetaTauAnalytic

def twoBall : RatBall := RatBall.point 2 0
def fourBall : RatBall := RatBall.point 4 0

structure ThetaEval where
  B : RatBall
  E : RatBall
  Ep : RatBall
  oneMinus : RatBall
  den : RatBall
  denSq : RatBall
  out : RatBall
  ok : Bool
  deriving Repr

def evalTheta (cBall LBall : RatBall) : ThetaEval :=
  let logs := checkLogs cBall
  let B := LBall.sub (logs.square.scale (1 / 2))
  let E := entropyBox cBall LBall
  let Ep := (logs.minus.sub logs.plus).scale (1 / 2)
  let oneMinus := oneBall.sub (cBall.pow 2)
  let den := oneMinus.mul B
  let denPrime := ((cBall.scale (-2)).mul B).add
    (oneMinus.mul (cBall.divAuto oneMinus))
  let num := ((E.add (cBall.mul Ep)).mul den).sub
    ((cBall.mul E).mul denPrime)
  let denSq := den.pow 2
  let frac := num.divAuto denSq
  let prefactor := twoBall.divAuto LBall
  let out := prefactor.mul (oneMinus.invAuto.add frac)
  ⟨B, E, Ep, oneMinus, den, denSq, out,
    LBall.invOK && oneMinus.invOK && denSq.invOK⟩

theorem evalTheta_sound {cBall LBall : RatBall} {c : ℂ}
    (hcBall : cBall.Holds c) (hc : ‖c‖ ≤ (1103 / 2500 : ℝ))
    (hL : LBall.Holds (Real.log 2 : ℂ))
    (hok : (evalTheta cBall LBall).ok = true) :
    (evalTheta cBall LBall).out.Holds (thetaParamDerivExplicit c) := by
  have hc' : ‖c‖ ≤ (contactRadiusQ : ℝ) := by
    simpa [contactRadiusQ] using hc
  have hlogs := checkLogs_sound hcBall hc'
  have hone := holds_point (1 : ℚ) 0
  have htwo := holds_point (2 : ℚ) 0
  have hB := holds_sub hL (holds_scale (1 / 2 : ℚ) hlogs.2.2)
  have hE := entropyBox_sound hcBall hc hL
  have hEp := holds_scale (1 / 2 : ℚ) (holds_sub hlogs.2.1 hlogs.1)
  have hcmul := holds_pow hcBall 2
  have hOneMinus := holds_sub hone hcmul
  have hDen := holds_mul hOneMinus hB
  have hOkL : LBall.invOK = true := by
    simpa [evalTheta] using
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).1
  have hOkOne : (oneBall.sub (cBall.pow 2)).invOK = true := by
    simpa [evalTheta] using
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).2
  have hOkDen : (((oneBall.sub (cBall.pow 2)).mul
      (LBall.sub ((checkLogs cBall).square.scale (1 / 2)))).pow 2).invOK = true := by
    simpa [evalTheta] using (Bool.and_eq_true_iff.mp hok).2
  have hcOver := holds_divAuto hcBall hOneMinus hOkOne
  have hDenPrime := holds_add
    (holds_mul (holds_scale (-2 : ℚ) hcBall) hB)
    (holds_mul hOneMinus hcOver)
  have hNum := holds_sub
    (holds_mul (holds_add hE (holds_mul hcBall hEp)) hDen)
    (holds_mul (holds_mul hcBall hE) hDenPrime)
  have hDenSq := holds_pow hDen 2
  have hFrac := holds_divAuto hNum hDenSq hOkDen
  have hPref := holds_divAuto htwo hL hOkL
  have hOut := holds_mul hPref (holds_add (holds_invAuto hOneMinus hOkOne) hFrac)
  convert hOut using 1 <;>
    simp [evalTheta, thetaParamDerivExplicit, biasBExt, entropyDeriv,
      oneBall, twoBall, GaussianRat.val, div_eq_mul_inv] <;> try ring <;> simp

structure TauEval where
  theta : ThetaEval
  jac : RatBall
  cPrime : RatBall
  out : RatBall
  ok : Bool
  deriving Repr

def evalTau (tauBall cBall LBall : RatBall) : TauEval :=
  let theta := evalTheta cBall LBall
  let jac := oneBall.sub (tauBall.mul theta.Ep)
  let cPrime := theta.E.divAuto jac
  let out := (theta.out.mul cPrime).sub fourBall
  ⟨theta, jac, cPrime, out,
    theta.ok && jac.invOK && out.acceptsUnit⟩

theorem evalTau_sound {tauBall cBall LBall : RatBall} {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau)
    (hcBall : cBall.Holds (fixedPointOnDisc tau))
    (hL : LBall.Holds (Real.log 2 : ℂ))
    (hok : (evalTau tauBall cBall LBall).ok = true) :
    ‖thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  let c := fixedPointOnDisc tau
  have hc := norm_fixedPointOnDisc_le htau
  have hThetaOK : (evalTheta cBall LBall).ok = true := by
    simpa [evalTau] using
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).1
  have hJacOK : (oneBall.sub (tauBall.mul (evalTheta cBall LBall).Ep)).invOK = true := by
    simpa [evalTau] using
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).2
  have hAccept : (evalTau tauBall cBall LBall).out.acceptsUnit = true :=
    (Bool.and_eq_true_iff.mp hok).2
  have hTheta := evalTheta_sound hcBall hc hL hThetaOK
  have hc' : ‖c‖ ≤ (contactRadiusQ : ℝ) := by
    simpa [contactRadiusQ] using hc
  have hlogs := checkLogs_sound hcBall hc'
  have hEp := holds_scale (1 / 2 : ℚ) (holds_sub hlogs.2.1 hlogs.1)
  have hE := entropyBox_sound hcBall hc hL
  have hJac := holds_sub (holds_point (1 : ℚ) 0) (holds_mul htauBall hEp)
  have hcPrime := holds_divAuto hE hJac hJacOK
  have hcPrime' : ((evalTheta cBall LBall).E.divAuto
      (oneBall.sub (tauBall.mul (evalTheta cBall LBall).Ep))).Holds
      (entropyExt c / (1 - tau * entropyDeriv c)) := by
    convert hcPrime using 1 <;>
      norm_num [evalTheta, oneBall, GaussianRat.val, entropyDeriv] <;> ring
  have hout := holds_sub (holds_mul hTheta hcPrime') (holds_point (4 : ℚ) 0)
  have hout' : (evalTau tauBall cBall LBall).out.Holds
      (thetaParamDerivExplicit c *
        (entropyExt c / (1 - tau * entropyDeriv c)) - 4) := by
    convert hout using 1 <;>
      norm_num [evalTau, oneBall, fourBall, GaussianRat.val, entropyDeriv] <;>
      try ring <;> simp [c]
  have hunit := acceptsUnit_sound hAccept hout'
  have hderiv := deriv_thetaParam_eq_explicit hc
  rw [thetaTauDerivExpr, hderiv]
  exact hunit

end GeneralCK.Certificates.E8DerivativeBallEvaluator
