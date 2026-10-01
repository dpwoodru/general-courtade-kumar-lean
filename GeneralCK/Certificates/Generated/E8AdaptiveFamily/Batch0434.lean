import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3472 : RatBall :=
  ⟨⟨-27/640, 253/640⟩, 3/1280⟩
def center3472 : GaussianRat :=
  ⟨-6970453/200000000, 289742037/1000000000⟩
def contact3472 : RatBall := localContactBall tau3472 center3472
def work3472 : RoundedTauEval :=
  evalTau precision tau3472 contact3472 logTwoBall

theorem center_sq3472 : (center3472.re : ℝ)^2 +
    (center3472.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3472]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3472 : work3472.theta.ok = true ∧
    work3472.jac.invOK = true ∧ acceptsUnitSq work3472.out = true := by
  norm_num [work3472, contact3472, tau3472, center3472, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3472 : CellCertificate where
  tauBall := tau3472
  contactCenter := center3472
  contactBall := contact3472
  work := work3472
  center_sq := center_sq3472
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3472.1
  jac_ok := checks3472.2.1
  accepted := checks3472.2.2

def tau3473 : RatBall :=
  ⟨⟨-5/128, 253/640⟩, 3/1280⟩
def center3473 : GaussianRat :=
  ⟨-16138267/500000000, 7246099/25000000⟩
def contact3473 : RatBall := localContactBall tau3473 center3473
def work3473 : RoundedTauEval :=
  evalTau precision tau3473 contact3473 logTwoBall

theorem center_sq3473 : (center3473.re : ℝ)^2 +
    (center3473.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3473]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3473 : work3473.theta.ok = true ∧
    work3473.jac.invOK = true ∧ acceptsUnitSq work3473.out = true := by
  norm_num [work3473, contact3473, tau3473, center3473, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3473 : CellCertificate where
  tauBall := tau3473
  contactCenter := center3473
  contactBall := contact3473
  work := work3473
  center_sq := center_sq3473
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3473.1
  jac_ok := checks3473.2.1
  accepted := checks3473.2.2

def tau3474 : RatBall :=
  ⟨⟨-27/640, 51/128⟩, 3/1280⟩
def center3474 : GaussianRat :=
  ⟨-34958801/1000000000, 14616047/50000000⟩
def contact3474 : RatBall := localContactBall tau3474 center3474
def work3474 : RoundedTauEval :=
  evalTau precision tau3474 contact3474 logTwoBall

theorem center_sq3474 : (center3474.re : ℝ)^2 +
    (center3474.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3474]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3474 : work3474.theta.ok = true ∧
    work3474.jac.invOK = true ∧ acceptsUnitSq work3474.out = true := by
  norm_num [work3474, contact3474, tau3474, center3474, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3474 : CellCertificate where
  tauBall := tau3474
  contactCenter := center3474
  contactBall := contact3474
  work := work3474
  center_sq := center_sq3474
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3474.1
  jac_ok := checks3474.2.1
  accepted := checks3474.2.2

def tau3475 : RatBall :=
  ⟨⟨-5/128, 51/128⟩, 3/1280⟩
def center3475 : GaussianRat :=
  ⟨-32375263/1000000000, 292424289/1000000000⟩
def contact3475 : RatBall := localContactBall tau3475 center3475
def work3475 : RoundedTauEval :=
  evalTau precision tau3475 contact3475 logTwoBall

theorem center_sq3475 : (center3475.re : ℝ)^2 +
    (center3475.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3475]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3475 : work3475.theta.ok = true ∧
    work3475.jac.invOK = true ∧ acceptsUnitSq work3475.out = true := by
  norm_num [work3475, contact3475, tau3475, center3475, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3475 : CellCertificate where
  tauBall := tau3475
  contactCenter := center3475
  contactBall := contact3475
  work := work3475
  center_sq := center_sq3475
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3475.1
  jac_ok := checks3475.2.1
  accepted := checks3475.2.2

def tau3476 : RatBall :=
  ⟨⟨-23/640, 249/640⟩, 3/1280⟩
def center3476 : GaussianRat :=
  ⟨-29521383/1000000000, 142399033/500000000⟩
def contact3476 : RatBall := localContactBall tau3476 center3476
def work3476 : RoundedTauEval :=
  evalTau precision tau3476 contact3476 logTwoBall

theorem center_sq3476 : (center3476.re : ℝ)^2 +
    (center3476.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3476]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3476 : work3476.theta.ok = true ∧
    work3476.jac.invOK = true ∧ acceptsUnitSq work3476.out = true := by
  norm_num [work3476, contact3476, tau3476, center3476, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3476 : CellCertificate where
  tauBall := tau3476
  contactCenter := center3476
  contactBall := contact3476
  work := work3476
  center_sq := center_sq3476
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3476.1
  jac_ok := checks3476.2.1
  accepted := checks3476.2.2

def tau3477 : RatBall :=
  ⟨⟨-21/640, 249/640⟩, 3/1280⟩
def center3477 : GaussianRat :=
  ⟨-26958403/1000000000, 284882077/1000000000⟩
def contact3477 : RatBall := localContactBall tau3477 center3477
def work3477 : RoundedTauEval :=
  evalTau precision tau3477 contact3477 logTwoBall

theorem center_sq3477 : (center3477.re : ℝ)^2 +
    (center3477.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3477]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3477 : work3477.theta.ok = true ∧
    work3477.jac.invOK = true ∧ acceptsUnitSq work3477.out = true := by
  norm_num [work3477, contact3477, tau3477, center3477, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3477 : CellCertificate where
  tauBall := tau3477
  contactCenter := center3477
  contactBall := contact3477
  work := work3477
  center_sq := center_sq3477
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3477.1
  jac_ok := checks3477.2.1
  accepted := checks3477.2.2

def tau3478 : RatBall :=
  ⟨⟨-23/640, 251/640⟩, 3/1280⟩
def center3478 : GaussianRat :=
  ⟨-14804897/500000000, 8980133/31250000⟩
def contact3478 : RatBall := localContactBall tau3478 center3478
def work3478 : RoundedTauEval :=
  evalTau precision tau3478 contact3478 logTwoBall

theorem center_sq3478 : (center3478.re : ℝ)^2 +
    (center3478.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3478]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3478 : work3478.theta.ok = true ∧
    work3478.jac.invOK = true ∧ acceptsUnitSq work3478.out = true := by
  norm_num [work3478, contact3478, tau3478, center3478, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3478 : CellCertificate where
  tauBall := tau3478
  contactCenter := center3478
  contactBall := contact3478
  work := work3478
  center_sq := center_sq3478
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3478.1
  jac_ok := checks3478.2.1
  accepted := checks3478.2.2

def tau3479 : RatBall :=
  ⟨⟨-21/640, 251/640⟩, 3/1280⟩
def center3479 : GaussianRat :=
  ⟨-1689949/62500000, 143724721/500000000⟩
def contact3479 : RatBall := localContactBall tau3479 center3479
def work3479 : RoundedTauEval :=
  evalTau precision tau3479 contact3479 logTwoBall

theorem center_sq3479 : (center3479.re : ℝ)^2 +
    (center3479.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3479]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3479 : work3479.theta.ok = true ∧
    work3479.jac.invOK = true ∧ acceptsUnitSq work3479.out = true := by
  norm_num [work3479, contact3479, tau3479, center3479, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3479 : CellCertificate where
  tauBall := tau3479
  contactCenter := center3479
  contactBall := contact3479
  work := work3479
  center_sq := center_sq3479
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3479.1
  jac_ok := checks3479.2.1
  accepted := checks3479.2.2

def cells : List CellCertificate := [cell3472, cell3473, cell3474, cell3475, cell3476, cell3477, cell3478, cell3479]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434
