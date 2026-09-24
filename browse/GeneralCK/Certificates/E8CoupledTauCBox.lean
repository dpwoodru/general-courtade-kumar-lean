import GeneralCK.Certificates.E8ThetaParamDerivativeExplicit
import GeneralCK.Certificates.DyadicLogSeries

/-!
# Coupled tau/contact-box refinement prototype

The contact box is refined by replaying the exact fixed-point identity
`c = tau * entropyExt c`.  Repeating `refinement_step` gives a proof-producing
interval iteration, beginning with `globalContactBall`.
-/

namespace GeneralCK.Certificates.E8CoupledTauCBox

open E8GaussianRatBall E8ComplexLogBoxChecker
open Reflection.ComplexEntropy Reflection.ComplexGlobalAnalytic
open E8ThetaTauAnalytic

def oneBall : RatBall := RatBall.point 1 0
def globalContactBall : RatBall := ⟨⟨0, 0⟩, 1103 / 2500⟩
def logTwoBall : RatBall :=
  ⟨⟨1386294361 / 2000000000, 0⟩, 1 / 2000000000⟩

theorem logTwoBall_holds : logTwoBall.Holds (Real.log 2 : ℂ) := by
  have h := DyadicLogSeries.pilot_log_two
  have hball : ‖(Real.log 2 : ℂ) - ((1386294361 / 2000000000 : ℚ) : ℂ)‖ ≤
      ((1 / 2000000000 : ℚ) : ℝ) := by
    have heq : (Real.log 2 : ℂ) -
      ((1386294361 / 2000000000 : ℚ) : ℂ) =
      ((Real.log 2 - (1386294361 / 2000000000 : ℝ) : ℝ) : ℂ) := by
        norm_num
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]
  simpa [logTwoBall, RatBall.Holds, E8ComplexBallKernel.InBall,
    GaussianRat.val] using hball

def entropyBox (cBall logTwoBall : RatBall) : RatBall :=
  let logs := checkLogs cBall
  logTwoBall.sub
    ((((oneBall.add cBall).mul logs.plus).add
      ((oneBall.sub cBall).mul logs.minus)).scale (1 / 2))

def fixedPointImageBox (tauBall cBall logTwoBall : RatBall) : RatBall :=
  tauBall.mul (entropyBox cBall logTwoBall)

def refineContact (tauBall cBall : RatBall) : RatBall :=
  fixedPointImageBox tauBall cBall logTwoBall

def contactIter (tauBall : RatBall) : ℕ → RatBall
  | 0 => globalContactBall
  | n + 1 => refineContact tauBall (contactIter tauBall n)

theorem globalContactBall_holds {tau : ℂ} (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) :
    globalContactBall.Holds (fixedPointOnDisc tau) := by
  have hc := norm_fixedPointOnDisc_le htau
  simpa [globalContactBall, RatBall.Holds, E8ComplexBallKernel.InBall,
    GaussianRat.val] using hc

theorem entropyBox_sound {cBall logTwoBall : RatBall} {c : ℂ}
    (hcBall : cBall.Holds c) (hc : ‖c‖ ≤ (1103 / 2500 : ℝ))
    (hlogTwo : logTwoBall.Holds (Real.log 2 : ℂ)) :
    (entropyBox cBall logTwoBall).Holds (entropyExt c) := by
  have hc' : ‖c‖ ≤ (contactRadiusQ : ℝ) := by
    simpa [contactRadiusQ] using hc
  have hlogs := checkLogs_sound hcBall hc'
  have hone := holds_point (1 : ℚ) 0
  have hprefp := holds_add hone hcBall
  have hprefm := holds_sub hone hcBall
  have htermP := holds_mul hprefp hlogs.1
  have htermM := holds_mul hprefm hlogs.2.1
  have hhalf := holds_scale (1 / 2 : ℚ) (holds_add htermP htermM)
  have hout := holds_sub hlogTwo hhalf
  convert hout using 1 <;> norm_num [entropyBox, oneBall, entropyExt,
    GaussianRat.val] <;> ring

/-- One executable interval-refinement step.  `contains = true` is reduced by
kernel evaluation to a rational inequality. -/
theorem refinement_step {tauBall current next logTwoBall : RatBall} {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau)
    (hcurrent : current.Holds (fixedPointOnDisc tau))
    (hlogTwo : logTwoBall.Holds (Real.log 2 : ℂ))
    (hnext : next.contains (fixedPointImageBox tauBall current logTwoBall) = true) :
    next.Holds (fixedPointOnDisc tau) := by
  have hc := norm_fixedPointOnDisc_le htau
  have hE := entropyBox_sound hcurrent hc hlogTwo
  have himage := holds_mul htauBall hE
  have hfixed := fixedPointOnDisc_fixed (htau.trans_lt (by norm_num))
  rw [hfixed]
  exact contains_sound hnext himage

theorem contactIter_holds {tauBall : RatBall} {tau : ℂ}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau) :
    ∀ n, (contactIter tauBall n).Holds (fixedPointOnDisc tau)
  | 0 => globalContactBall_holds htau
  | n + 1 => by
      have hc := contactIter_holds htau htauBall n
      have hE := entropyBox_sound hc (norm_fixedPointOnDisc_le htau) logTwoBall_holds
      have himage := holds_mul htauBall hE
      change (fixedPointImageBox tauBall (contactIter tauBall n) logTwoBall).Holds
        (fixedPointOnDisc tau)
      rw [fixedPointOnDisc_fixed (htau.trans_lt (by norm_num))]
      exact himage

def zeroBall : RatBall := RatBall.point 0 0

/-- Smallest closed coupled-box replay: the exact tau-zero box refines the
global contact ball to the exact zero contact box by computation. -/
theorem coupled_zero_pilot : zeroBall.Holds (fixedPointOnDisc 0) := by
  apply refinement_step (tauBall := zeroBall) (current := globalContactBall)
    (logTwoBall := logTwoBall) (tau := 0)
  · norm_num
  · convert holds_point (0 : ℚ) 0 using 1 <;>
      norm_num [zeroBall, GaussianRat.val]
  · exact globalContactBall_holds (by norm_num)
  · exact logTwoBall_holds
  · norm_num [RatBall.contains, fixedPointImageBox, zeroBall, RatBall.mul,
      RatBall.point, GaussianRat.mul, GaussianRat.add, GaussianRat.neg, GaussianRat.l1]

end GeneralCK.Certificates.E8CoupledTauCBox
