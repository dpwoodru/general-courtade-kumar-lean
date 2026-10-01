import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3784 : RatBall :=
  ⟨⟨99/640, 231/640⟩, 3/1280⟩
def center3784 : GaussianRat :=
  ⟨122126333/1000000000, 127243109/500000000⟩
def contact3784 : RatBall := localContactBall tau3784 center3784
def work3784 : RoundedTauEval :=
  evalTau precision tau3784 contact3784 logTwoBall

theorem center_sq3784 : (center3784.re : ℝ)^2 +
    (center3784.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3784]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3784 : work3784.theta.ok = true ∧
    work3784.jac.invOK = true ∧ acceptsUnitSq work3784.out = true := by
  norm_num [work3784, contact3784, tau3784, center3784, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell3784 : CellCertificate where
  tauBall := tau3784
  contactCenter := center3784
  contactBall := contact3784
  work := work3784
  center_sq := center_sq3784
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3784.1
  jac_ok := checks3784.2.1
  accepted := checks3784.2.2

def tau3785 : RatBall :=
  ⟨⟨101/640, 229/640⟩, 3/1280⟩
def center3785 : GaussianRat :=
  ⟨62102193/500000000, 7868253/31250000⟩
def contact3785 : RatBall := localContactBall tau3785 center3785
def work3785 : RoundedTauEval :=
  evalTau precision tau3785 contact3785 logTwoBall

theorem center_sq3785 : (center3785.re : ℝ)^2 +
    (center3785.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3785]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3785 : work3785.theta.ok = true ∧
    work3785.jac.invOK = true ∧ acceptsUnitSq work3785.out = true := by
  norm_num [work3785, contact3785, tau3785, center3785, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell3785 : CellCertificate where
  tauBall := tau3785
  contactCenter := center3785
  contactBall := contact3785
  work := work3785
  center_sq := center_sq3785
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3785.1
  jac_ok := checks3785.2.1
  accepted := checks3785.2.2

def tau3786 : RatBall :=
  ⟨⟨103/640, 229/640⟩, 3/1280⟩
def center3786 : GaussianRat :=
  ⟨126587587/1000000000, 125734431/500000000⟩
def contact3786 : RatBall := localContactBall tau3786 center3786
def work3786 : RoundedTauEval :=
  evalTau precision tau3786 contact3786 logTwoBall

theorem center_sq3786 : (center3786.re : ℝ)^2 +
    (center3786.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3786]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3786 : work3786.theta.ok = true ∧
    work3786.jac.invOK = true ∧ acceptsUnitSq work3786.out = true := by
  norm_num [work3786, contact3786, tau3786, center3786, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell3786 : CellCertificate where
  tauBall := tau3786
  contactCenter := center3786
  contactBall := contact3786
  work := work3786
  center_sq := center_sq3786
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3786.1
  jac_ok := checks3786.2.1
  accepted := checks3786.2.2

def tau3787 : RatBall :=
  ⟨⟨101/640, 231/640⟩, 3/1280⟩
def center3787 : GaussianRat :=
  ⟨15564887/125000000, 254172071/1000000000⟩
def contact3787 : RatBall := localContactBall tau3787 center3787
def work3787 : RoundedTauEval :=
  evalTau precision tau3787 contact3787 logTwoBall

theorem center_sq3787 : (center3787.re : ℝ)^2 +
    (center3787.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3787]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3787 : work3787.theta.ok = true ∧
    work3787.jac.invOK = true ∧ acceptsUnitSq work3787.out = true := by
  norm_num [work3787, contact3787, tau3787, center3787, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell3787 : CellCertificate where
  tauBall := tau3787
  contactCenter := center3787
  contactBall := contact3787
  work := work3787
  center_sq := center_sq3787
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3787.1
  jac_ok := checks3787.2.1
  accepted := checks3787.2.2

def tau3788 : RatBall :=
  ⟨⟨103/640, 231/640⟩, 3/1280⟩
def center3788 : GaussianRat :=
  ⟨63453799/500000000, 253852567/1000000000⟩
def contact3788 : RatBall := localContactBall tau3788 center3788
def work3788 : RoundedTauEval :=
  evalTau precision tau3788 contact3788 logTwoBall

theorem center_sq3788 : (center3788.re : ℝ)^2 +
    (center3788.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3788]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3788 : work3788.theta.ok = true ∧
    work3788.jac.invOK = true ∧ acceptsUnitSq work3788.out = true := by
  norm_num [work3788, contact3788, tau3788, center3788, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell3788 : CellCertificate where
  tauBall := tau3788
  contactCenter := center3788
  contactBall := contact3788
  work := work3788
  center_sq := center_sq3788
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3788.1
  jac_ok := checks3788.2.1
  accepted := checks3788.2.2

def tau3789 : RatBall :=
  ⟨⟨109/640, 45/128⟩, 3/1280⟩
def center3789 : GaussianRat :=
  ⟨26610681/200000000, 245766093/1000000000⟩
def contact3789 : RatBall := localContactBall tau3789 center3789
def work3789 : RoundedTauEval :=
  evalTau precision tau3789 contact3789 logTwoBall

theorem center_sq3789 : (center3789.re : ℝ)^2 +
    (center3789.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3789]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3789 : work3789.theta.ok = true ∧
    work3789.jac.invOK = true ∧ acceptsUnitSq work3789.out = true := by
  norm_num [work3789, contact3789, tau3789, center3789, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell3789 : CellCertificate where
  tauBall := tau3789
  contactCenter := center3789
  contactBall := contact3789
  work := work3789
  center_sq := center_sq3789
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3789.1
  jac_ok := checks3789.2.1
  accepted := checks3789.2.2

def tau3790 : RatBall :=
  ⟨⟨111/640, 45/128⟩, 3/1280⟩
def center3790 : GaussianRat :=
  ⟨67704553/500000000, 6135977/25000000⟩
def contact3790 : RatBall := localContactBall tau3790 center3790
def work3790 : RoundedTauEval :=
  evalTau precision tau3790 contact3790 logTwoBall

theorem center_sq3790 : (center3790.re : ℝ)^2 +
    (center3790.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3790]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3790 : work3790.theta.ok = true ∧
    work3790.jac.invOK = true ∧ acceptsUnitSq work3790.out = true := by
  norm_num [work3790, contact3790, tau3790, center3790, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell3790 : CellCertificate where
  tauBall := tau3790
  contactCenter := center3790
  contactBall := contact3790
  work := work3790
  center_sq := center_sq3790
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3790.1
  jac_ok := checks3790.2.1
  accepted := checks3790.2.2

def tau3791 : RatBall :=
  ⟨⟨109/640, 227/640⟩, 3/1280⟩
def center3791 : GaussianRat :=
  ⟨133380131/1000000000, 248126483/1000000000⟩
def contact3791 : RatBall := localContactBall tau3791 center3791
def work3791 : RoundedTauEval :=
  evalTau precision tau3791 contact3791 logTwoBall

theorem center_sq3791 : (center3791.re : ℝ)^2 +
    (center3791.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3791]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3791 : work3791.theta.ok = true ∧
    work3791.jac.invOK = true ∧ acceptsUnitSq work3791.out = true := by
  norm_num [work3791, contact3791, tau3791, center3791, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell3791 : CellCertificate where
  tauBall := tau3791
  contactCenter := center3791
  contactBall := contact3791
  work := work3791
  center_sq := center_sq3791
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3791.1
  jac_ok := checks3791.2.1
  accepted := checks3791.2.2

def cells : List CellCertificate := [cell3784, cell3785, cell3786, cell3787, cell3788, cell3789, cell3790, cell3791]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473
