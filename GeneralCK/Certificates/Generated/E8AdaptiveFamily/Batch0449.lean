import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3592 : RatBall :=
  ⟨⟨5/128, 253/640⟩, 3/1280⟩
def center3592 : GaussianRat :=
  ⟨16138267/500000000, 7246099/25000000⟩
def contact3592 : RatBall := localContactBall tau3592 center3592
def work3592 : RoundedTauEval :=
  evalTau precision tau3592 contact3592 logTwoBall

theorem center_sq3592 : (center3592.re : ℝ)^2 +
    (center3592.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3592]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3592 : work3592.theta.ok = true ∧
    work3592.jac.invOK = true ∧ acceptsUnitSq work3592.out = true := by
  norm_num [work3592, contact3592, tau3592, center3592, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3592 : CellCertificate where
  tauBall := tau3592
  contactCenter := center3592
  contactBall := contact3592
  work := work3592
  center_sq := center_sq3592
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3592.1
  jac_ok := checks3592.2.1
  accepted := checks3592.2.2

def tau3593 : RatBall :=
  ⟨⟨27/640, 253/640⟩, 3/1280⟩
def center3593 : GaussianRat :=
  ⟨6970453/200000000, 289742037/1000000000⟩
def contact3593 : RatBall := localContactBall tau3593 center3593
def work3593 : RoundedTauEval :=
  evalTau precision tau3593 contact3593 logTwoBall

theorem center_sq3593 : (center3593.re : ℝ)^2 +
    (center3593.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3593]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3593 : work3593.theta.ok = true ∧
    work3593.jac.invOK = true ∧ acceptsUnitSq work3593.out = true := by
  norm_num [work3593, contact3593, tau3593, center3593, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3593 : CellCertificate where
  tauBall := tau3593
  contactCenter := center3593
  contactBall := contact3593
  work := work3593
  center_sq := center_sq3593
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3593.1
  jac_ok := checks3593.2.1
  accepted := checks3593.2.2

def tau3594 : RatBall :=
  ⟨⟨5/128, 51/128⟩, 3/1280⟩
def center3594 : GaussianRat :=
  ⟨32375263/1000000000, 292424289/1000000000⟩
def contact3594 : RatBall := localContactBall tau3594 center3594
def work3594 : RoundedTauEval :=
  evalTau precision tau3594 contact3594 logTwoBall

theorem center_sq3594 : (center3594.re : ℝ)^2 +
    (center3594.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3594]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3594 : work3594.theta.ok = true ∧
    work3594.jac.invOK = true ∧ acceptsUnitSq work3594.out = true := by
  norm_num [work3594, contact3594, tau3594, center3594, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3594 : CellCertificate where
  tauBall := tau3594
  contactCenter := center3594
  contactBall := contact3594
  work := work3594
  center_sq := center_sq3594
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3594.1
  jac_ok := checks3594.2.1
  accepted := checks3594.2.2

def tau3595 : RatBall :=
  ⟨⟨27/640, 51/128⟩, 3/1280⟩
def center3595 : GaussianRat :=
  ⟨34958801/1000000000, 14616047/50000000⟩
def contact3595 : RatBall := localContactBall tau3595 center3595
def work3595 : RoundedTauEval :=
  evalTau precision tau3595 contact3595 logTwoBall

theorem center_sq3595 : (center3595.re : ℝ)^2 +
    (center3595.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3595]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3595 : work3595.theta.ok = true ∧
    work3595.jac.invOK = true ∧ acceptsUnitSq work3595.out = true := by
  norm_num [work3595, contact3595, tau3595, center3595, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3595 : CellCertificate where
  tauBall := tau3595
  contactCenter := center3595
  contactBall := contact3595
  work := work3595
  center_sq := center_sq3595
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3595.1
  jac_ok := checks3595.2.1
  accepted := checks3595.2.2

def tau3596 : RatBall :=
  ⟨⟨29/640, 253/640⟩, 3/1280⟩
def center3596 : GaussianRat :=
  ⟨18713263/500000000, 289632371/1000000000⟩
def contact3596 : RatBall := localContactBall tau3596 center3596
def work3596 : RoundedTauEval :=
  evalTau precision tau3596 contact3596 logTwoBall

theorem center_sq3596 : (center3596.re : ℝ)^2 +
    (center3596.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3596]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3596 : work3596.theta.ok = true ∧
    work3596.jac.invOK = true ∧ acceptsUnitSq work3596.out = true := by
  norm_num [work3596, contact3596, tau3596, center3596, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3596 : CellCertificate where
  tauBall := tau3596
  contactCenter := center3596
  contactBall := contact3596
  work := work3596
  center_sq := center_sq3596
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3596.1
  jac_ok := checks3596.2.1
  accepted := checks3596.2.2

def tau3597 : RatBall :=
  ⟨⟨31/640, 253/640⟩, 3/1280⟩
def center3597 : GaussianRat :=
  ⟨9999803/250000000, 36189373/125000000⟩
def contact3597 : RatBall := localContactBall tau3597 center3597
def work3597 : RoundedTauEval :=
  evalTau precision tau3597 contact3597 logTwoBall

theorem center_sq3597 : (center3597.re : ℝ)^2 +
    (center3597.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3597]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3597 : work3597.theta.ok = true ∧
    work3597.jac.invOK = true ∧ acceptsUnitSq work3597.out = true := by
  norm_num [work3597, contact3597, tau3597, center3597, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3597 : CellCertificate where
  tauBall := tau3597
  contactCenter := center3597
  contactBall := contact3597
  work := work3597
  center_sq := center_sq3597
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3597.1
  jac_ok := checks3597.2.1
  accepted := checks3597.2.2

def tau3598 : RatBall :=
  ⟨⟨29/640, 51/128⟩, 3/1280⟩
def center3598 : GaussianRat :=
  ⟨2346303/62500000, 292209741/1000000000⟩
def contact3598 : RatBall := localContactBall tau3598 center3598
def work3598 : RoundedTauEval :=
  evalTau precision tau3598 contact3598 logTwoBall

theorem center_sq3598 : (center3598.re : ℝ)^2 +
    (center3598.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3598]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3598 : work3598.theta.ok = true ∧
    work3598.jac.invOK = true ∧ acceptsUnitSq work3598.out = true := by
  norm_num [work3598, contact3598, tau3598, center3598, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3598 : CellCertificate where
  tauBall := tau3598
  contactCenter := center3598
  contactBall := contact3598
  work := work3598
  center_sq := center_sq3598
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3598.1
  jac_ok := checks3598.2.1
  accepted := checks3598.2.2

def tau3599 : RatBall :=
  ⟨⟨31/640, 51/128⟩, 3/1280⟩
def center3599 : GaussianRat :=
  ⟨20060649/500000000, 146045357/500000000⟩
def contact3599 : RatBall := localContactBall tau3599 center3599
def work3599 : RoundedTauEval :=
  evalTau precision tau3599 contact3599 logTwoBall

theorem center_sq3599 : (center3599.re : ℝ)^2 +
    (center3599.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3599]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3599 : work3599.theta.ok = true ∧
    work3599.jac.invOK = true ∧ acceptsUnitSq work3599.out = true := by
  norm_num [work3599, contact3599, tau3599, center3599, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3599 : CellCertificate where
  tauBall := tau3599
  contactCenter := center3599
  contactBall := contact3599
  work := work3599
  center_sq := center_sq3599
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3599.1
  jac_ok := checks3599.2.1
  accepted := checks3599.2.2

def cells : List CellCertificate := [cell3592, cell3593, cell3594, cell3595, cell3596, cell3597, cell3598, cell3599]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449
