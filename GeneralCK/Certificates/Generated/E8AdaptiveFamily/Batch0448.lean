import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3584 : RatBall :=
  ⟨⟨5/128, 249/640⟩, 3/1280⟩
def center3584 : GaussianRat :=
  ⟨32083143/1000000000, 142353243/500000000⟩
def contact3584 : RatBall := localContactBall tau3584 center3584
def work3584 : RoundedTauEval :=
  evalTau precision tau3584 contact3584 logTwoBall

theorem center_sq3584 : (center3584.re : ℝ)^2 +
    (center3584.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3584]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3584 : work3584.theta.ok = true ∧
    work3584.jac.invOK = true ∧ acceptsUnitSq work3584.out = true := by
  norm_num [work3584, contact3584, tau3584, center3584, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3584 : CellCertificate where
  tauBall := tau3584
  contactCenter := center3584
  contactBall := contact3584
  work := work3584
  center_sq := center_sq3584
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3584.1
  jac_ok := checks3584.2.1
  accepted := checks3584.2.2

def tau3585 : RatBall :=
  ⟨⟨27/640, 249/640⟩, 3/1280⟩
def center3585 : GaussianRat :=
  ⟨34643579/1000000000, 56921471/200000000⟩
def contact3585 : RatBall := localContactBall tau3585 center3585
def work3585 : RoundedTauEval :=
  evalTau precision tau3585 contact3585 logTwoBall

theorem center_sq3585 : (center3585.re : ℝ)^2 +
    (center3585.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3585]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3585 : work3585.theta.ok = true ∧
    work3585.jac.invOK = true ∧ acceptsUnitSq work3585.out = true := by
  norm_num [work3585, contact3585, tau3585, center3585, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3585 : CellCertificate where
  tauBall := tau3585
  contactCenter := center3585
  contactBall := contact3585
  work := work3585
  center_sq := center_sq3585
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3585.1
  jac_ok := checks3585.2.1
  accepted := checks3585.2.2

def tau3586 : RatBall :=
  ⟨⟨5/128, 251/640⟩, 3/1280⟩
def center3586 : GaussianRat :=
  ⟨32179167/1000000000, 57454279/200000000⟩
def contact3586 : RatBall := localContactBall tau3586 center3586
def work3586 : RoundedTauEval :=
  evalTau precision tau3586 contact3586 logTwoBall

theorem center_sq3586 : (center3586.re : ℝ)^2 +
    (center3586.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3586]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3586 : work3586.theta.ok = true ∧
    work3586.jac.invOK = true ∧ acceptsUnitSq work3586.out = true := by
  norm_num [work3586, contact3586, tau3586, center3586, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3586 : CellCertificate where
  tauBall := tau3586
  contactCenter := center3586
  contactBall := contact3586
  work := work3586
  center_sq := center_sq3586
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3586.1
  jac_ok := checks3586.2.1
  accepted := checks3586.2.2

def tau3587 : RatBall :=
  ⟨⟨27/640, 251/640⟩, 3/1280⟩
def center3587 : GaussianRat :=
  ⟨17373599/500000000, 287170877/1000000000⟩
def contact3587 : RatBall := localContactBall tau3587 center3587
def work3587 : RoundedTauEval :=
  evalTau precision tau3587 contact3587 logTwoBall

theorem center_sq3587 : (center3587.re : ℝ)^2 +
    (center3587.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3587]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3587 : work3587.theta.ok = true ∧
    work3587.jac.invOK = true ∧ acceptsUnitSq work3587.out = true := by
  norm_num [work3587, contact3587, tau3587, center3587, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3587 : CellCertificate where
  tauBall := tau3587
  contactCenter := center3587
  contactBall := contact3587
  work := work3587
  center_sq := center_sq3587
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3587.1
  jac_ok := checks3587.2.1
  accepted := checks3587.2.2

def tau3588 : RatBall :=
  ⟨⟨29/640, 249/640⟩, 3/1280⟩
def center3588 : GaussianRat :=
  ⟨37202587/1000000000, 284500691/1000000000⟩
def contact3588 : RatBall := localContactBall tau3588 center3588
def work3588 : RoundedTauEval :=
  evalTau precision tau3588 contact3588 logTwoBall

theorem center_sq3588 : (center3588.re : ℝ)^2 +
    (center3588.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3588]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3588 : work3588.theta.ok = true ∧
    work3588.jac.invOK = true ∧ acceptsUnitSq work3588.out = true := by
  norm_num [work3588, contact3588, tau3588, center3588, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3588 : CellCertificate where
  tauBall := tau3588
  contactCenter := center3588
  contactBall := contact3588
  work := work3588
  center_sq := center_sq3588
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3588.1
  jac_ok := checks3588.2.1
  accepted := checks3588.2.2

def tau3589 : RatBall :=
  ⟨⟨31/640, 249/640⟩, 3/1280⟩
def center3589 : GaussianRat :=
  ⟨19880031/500000000, 56877303/200000000⟩
def contact3589 : RatBall := localContactBall tau3589 center3589
def work3589 : RoundedTauEval :=
  evalTau precision tau3589 contact3589 logTwoBall

theorem center_sq3589 : (center3589.re : ℝ)^2 +
    (center3589.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3589]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3589 : work3589.theta.ok = true ∧
    work3589.jac.invOK = true ∧ acceptsUnitSq work3589.out = true := by
  norm_num [work3589, contact3589, tau3589, center3589, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3589 : CellCertificate where
  tauBall := tau3589
  contactCenter := center3589
  contactBall := contact3589
  work := work3589
  center_sq := center_sq3589
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3589.1
  jac_ok := checks3589.2.1
  accepted := checks3589.2.2

def tau3590 : RatBall :=
  ⟨⟨29/640, 251/640⟩, 3/1280⟩
def center3590 : GaussianRat :=
  ⟨1865689/50000000, 287062723/1000000000⟩
def contact3590 : RatBall := localContactBall tau3590 center3590
def work3590 : RoundedTauEval :=
  evalTau precision tau3590 contact3590 logTwoBall

theorem center_sq3590 : (center3590.re : ℝ)^2 +
    (center3590.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3590]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3590 : work3590.theta.ok = true ∧
    work3590.jac.invOK = true ∧ acceptsUnitSq work3590.out = true := by
  norm_num [work3590, contact3590, tau3590, center3590, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3590 : CellCertificate where
  tauBall := tau3590
  contactCenter := center3590
  contactBall := contact3590
  work := work3590
  center_sq := center_sq3590
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3590.1
  jac_ok := checks3590.2.1
  accepted := checks3590.2.2

def tau3591 : RatBall :=
  ⟨⟨31/640, 251/640⟩, 3/1280⟩
def center3591 : GaussianRat :=
  ⟨4984851/125000000, 286946953/1000000000⟩
def contact3591 : RatBall := localContactBall tau3591 center3591
def work3591 : RoundedTauEval :=
  evalTau precision tau3591 contact3591 logTwoBall

theorem center_sq3591 : (center3591.re : ℝ)^2 +
    (center3591.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3591]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3591 : work3591.theta.ok = true ∧
    work3591.jac.invOK = true ∧ acceptsUnitSq work3591.out = true := by
  norm_num [work3591, contact3591, tau3591, center3591, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3591 : CellCertificate where
  tauBall := tau3591
  contactCenter := center3591
  contactBall := contact3591
  work := work3591
  center_sq := center_sq3591
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3591.1
  jac_ok := checks3591.2.1
  accepted := checks3591.2.2

def cells : List CellCertificate := [cell3584, cell3585, cell3586, cell3587, cell3588, cell3589, cell3590, cell3591]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448
