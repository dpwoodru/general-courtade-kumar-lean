import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3520 : RatBall :=
  ⟨⟨-3/640, 253/640⟩, 3/1280⟩
def center3520 : GaussianRat :=
  ⟨-3877403/1000000000, 36306181/125000000⟩
def contact3520 : RatBall := localContactBall tau3520 center3520
def work3520 : RoundedTauEval :=
  evalTau precision tau3520 contact3520 logTwoBall

theorem center_sq3520 : (center3520.re : ℝ)^2 +
    (center3520.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3520]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3520 : work3520.theta.ok = true ∧
    work3520.jac.invOK = true ∧ acceptsUnitSq work3520.out = true := by
  norm_num [work3520, contact3520, tau3520, center3520, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3520 : CellCertificate where
  tauBall := tau3520
  contactCenter := center3520
  contactBall := contact3520
  work := work3520
  center_sq := center_sq3520
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3520.1
  jac_ok := checks3520.2.1
  accepted := checks3520.2.2

def tau3521 : RatBall :=
  ⟨⟨-1/640, 253/640⟩, 3/1280⟩
def center3521 : GaussianRat :=
  ⟨-646243/500000000, 72614333/250000000⟩
def contact3521 : RatBall := localContactBall tau3521 center3521
def work3521 : RoundedTauEval :=
  evalTau precision tau3521 contact3521 logTwoBall

theorem center_sq3521 : (center3521.re : ℝ)^2 +
    (center3521.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3521]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3521 : work3521.theta.ok = true ∧
    work3521.jac.invOK = true ∧ acceptsUnitSq work3521.out = true := by
  norm_num [work3521, contact3521, tau3521, center3521, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3521 : CellCertificate where
  tauBall := tau3521
  contactCenter := center3521
  contactBall := contact3521
  work := work3521
  center_sq := center_sq3521
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3521.1
  jac_ok := checks3521.2.1
  accepted := checks3521.2.2

def tau3522 : RatBall :=
  ⟨⟨-3/640, 51/128⟩, 3/1280⟩
def center3522 : GaussianRat :=
  ⟨-3889311/1000000000, 293038261/1000000000⟩
def contact3522 : RatBall := localContactBall tau3522 center3522
def work3522 : RoundedTauEval :=
  evalTau precision tau3522 contact3522 logTwoBall

theorem center_sq3522 : (center3522.re : ℝ)^2 +
    (center3522.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3522]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3522 : work3522.theta.ok = true ∧
    work3522.jac.invOK = true ∧ acceptsUnitSq work3522.out = true := by
  norm_num [work3522, contact3522, tau3522, center3522, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3522 : CellCertificate where
  tauBall := tau3522
  contactCenter := center3522
  contactBall := contact3522
  work := work3522
  center_sq := center_sq3522
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3522.1
  jac_ok := checks3522.2.1
  accepted := checks3522.2.2

def tau3523 : RatBall :=
  ⟨⟨-1/640, 51/128⟩, 3/1280⟩
def center3523 : GaussianRat :=
  ⟨-162057/125000000, 58609251/200000000⟩
def contact3523 : RatBall := localContactBall tau3523 center3523
def work3523 : RoundedTauEval :=
  evalTau precision tau3523 contact3523 logTwoBall

theorem center_sq3523 : (center3523.re : ℝ)^2 +
    (center3523.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3523]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3523 : work3523.theta.ok = true ∧
    work3523.jac.invOK = true ∧ acceptsUnitSq work3523.out = true := by
  norm_num [work3523, contact3523, tau3523, center3523, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3523 : CellCertificate where
  tauBall := tau3523
  contactCenter := center3523
  contactBall := contact3523
  work := work3523
  center_sq := center_sq3523
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3523.1
  jac_ok := checks3523.2.1
  accepted := checks3523.2.2

def tau3524 : RatBall :=
  ⟨⟨1/640, 249/640⟩, 3/1280⟩
def center3524 : GaussianRat :=
  ⟨1284711/1000000000, 285303029/1000000000⟩
def contact3524 : RatBall := localContactBall tau3524 center3524
def work3524 : RoundedTauEval :=
  evalTau precision tau3524 contact3524 logTwoBall

theorem center_sq3524 : (center3524.re : ℝ)^2 +
    (center3524.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3524]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3524 : work3524.theta.ok = true ∧
    work3524.jac.invOK = true ∧ acceptsUnitSq work3524.out = true := by
  norm_num [work3524, contact3524, tau3524, center3524, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3524 : CellCertificate where
  tauBall := tau3524
  contactCenter := center3524
  contactBall := contact3524
  work := work3524
  center_sq := center_sq3524
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3524.1
  jac_ok := checks3524.2.1
  accepted := checks3524.2.2

def tau3525 : RatBall :=
  ⟨⟨3/640, 249/640⟩, 3/1280⟩
def center3525 : GaussianRat :=
  ⟨3854079/1000000000, 142647681/500000000⟩
def contact3525 : RatBall := localContactBall tau3525 center3525
def work3525 : RoundedTauEval :=
  evalTau precision tau3525 contact3525 logTwoBall

theorem center_sq3525 : (center3525.re : ℝ)^2 +
    (center3525.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3525]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3525 : work3525.theta.ok = true ∧
    work3525.jac.invOK = true ∧ acceptsUnitSq work3525.out = true := by
  norm_num [work3525, contact3525, tau3525, center3525, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3525 : CellCertificate where
  tauBall := tau3525
  contactCenter := center3525
  contactBall := contact3525
  work := work3525
  center_sq := center_sq3525
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3525.1
  jac_ok := checks3525.2.1
  accepted := checks3525.2.2

def tau3526 : RatBall :=
  ⟨⟨1/640, 251/640⟩, 3/1280⟩
def center3526 : GaussianRat :=
  ⟨1288571/1000000000, 287876293/1000000000⟩
def contact3526 : RatBall := localContactBall tau3526 center3526
def work3526 : RoundedTauEval :=
  evalTau precision tau3526 contact3526 logTwoBall

theorem center_sq3526 : (center3526.re : ℝ)^2 +
    (center3526.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3526]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3526 : work3526.theta.ok = true ∧
    work3526.jac.invOK = true ∧ acceptsUnitSq work3526.out = true := by
  norm_num [work3526, contact3526, tau3526, center3526, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3526 : CellCertificate where
  tauBall := tau3526
  contactCenter := center3526
  contactBall := contact3526
  work := work3526
  center_sq := center_sq3526
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3526.1
  jac_ok := checks3526.2.1
  accepted := checks3526.2.2

def tau3527 : RatBall :=
  ⟨⟨3/640, 251/640⟩, 3/1280⟩
def center3527 : GaussianRat :=
  ⟨193283/50000000, 143934259/500000000⟩
def contact3527 : RatBall := localContactBall tau3527 center3527
def work3527 : RoundedTauEval :=
  evalTau precision tau3527 contact3527 logTwoBall

theorem center_sq3527 : (center3527.re : ℝ)^2 +
    (center3527.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3527]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3527 : work3527.theta.ok = true ∧
    work3527.jac.invOK = true ∧ acceptsUnitSq work3527.out = true := by
  norm_num [work3527, contact3527, tau3527, center3527, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3527 : CellCertificate where
  tauBall := tau3527
  contactCenter := center3527
  contactBall := contact3527
  work := work3527
  center_sq := center_sq3527
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3527.1
  jac_ok := checks3527.2.1
  accepted := checks3527.2.2

def cells : List CellCertificate := [cell3520, cell3521, cell3522, cell3523, cell3524, cell3525, cell3526, cell3527]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440
