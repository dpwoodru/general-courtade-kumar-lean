import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3416 : RatBall :=
  ⟨⟨-41/640, 247/640⟩, 3/1280⟩
def center3416 : GaussianRat :=
  ⟨-52366871/1000000000, 70290053/250000000⟩
def contact3416 : RatBall := localContactBall tau3416 center3416
def work3416 : RoundedTauEval :=
  evalTau precision tau3416 contact3416 logTwoBall

theorem center_sq3416 : (center3416.re : ℝ)^2 +
    (center3416.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3416]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3416 : work3416.theta.ok = true ∧
    work3416.jac.invOK = true ∧ acceptsUnitSq work3416.out = true := by
  norm_num [work3416, contact3416, tau3416, center3416, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3416 : CellCertificate where
  tauBall := tau3416
  contactCenter := center3416
  contactBall := contact3416
  work := work3416
  center_sq := center_sq3416
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3416.1
  jac_ok := checks3416.2.1
  accepted := checks3416.2.2

def tau3417 : RatBall :=
  ⟨⟨-39/640, 49/128⟩, 3/1280⟩
def center3417 : GaussianRat :=
  ⟨-49681259/1000000000, 139385581/500000000⟩
def contact3417 : RatBall := localContactBall tau3417 center3417
def work3417 : RoundedTauEval :=
  evalTau precision tau3417 contact3417 logTwoBall

theorem center_sq3417 : (center3417.re : ℝ)^2 +
    (center3417.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3417]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3417 : work3417.theta.ok = true ∧
    work3417.jac.invOK = true ∧ acceptsUnitSq work3417.out = true := by
  norm_num [work3417, contact3417, tau3417, center3417, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3417 : CellCertificate where
  tauBall := tau3417
  contactCenter := center3417
  contactBall := contact3417
  work := work3417
  center_sq := center_sq3417
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3417.1
  jac_ok := checks3417.2.1
  accepted := checks3417.2.2

def tau3418 : RatBall :=
  ⟨⟨-37/640, 49/128⟩, 3/1280⟩
def center3418 : GaussianRat :=
  ⟨-23572771/500000000, 278911223/1000000000⟩
def contact3418 : RatBall := localContactBall tau3418 center3418
def work3418 : RoundedTauEval :=
  evalTau precision tau3418 contact3418 logTwoBall

theorem center_sq3418 : (center3418.re : ℝ)^2 +
    (center3418.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3418]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3418 : work3418.theta.ok = true ∧
    work3418.jac.invOK = true ∧ acceptsUnitSq work3418.out = true := by
  norm_num [work3418, contact3418, tau3418, center3418, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3418 : CellCertificate where
  tauBall := tau3418
  contactCenter := center3418
  contactBall := contact3418
  work := work3418
  center_sq := center_sq3418
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3418.1
  jac_ok := checks3418.2.1
  accepted := checks3418.2.2

def tau3419 : RatBall :=
  ⟨⟨-39/640, 247/640⟩, 3/1280⟩
def center3419 : GaussianRat :=
  ⟨-49825917/1000000000, 281309513/1000000000⟩
def contact3419 : RatBall := localContactBall tau3419 center3419
def work3419 : RoundedTauEval :=
  evalTau precision tau3419 contact3419 logTwoBall

theorem center_sq3419 : (center3419.re : ℝ)^2 +
    (center3419.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3419]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3419 : work3419.theta.ok = true ∧
    work3419.jac.invOK = true ∧ acceptsUnitSq work3419.out = true := by
  norm_num [work3419, contact3419, tau3419, center3419, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3419 : CellCertificate where
  tauBall := tau3419
  contactCenter := center3419
  contactBall := contact3419
  work := work3419
  center_sq := center_sq3419
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3419.1
  jac_ok := checks3419.2.1
  accepted := checks3419.2.2

def tau3420 : RatBall :=
  ⟨⟨-37/640, 247/640⟩, 3/1280⟩
def center3420 : GaussianRat :=
  ⟨-11820737/250000000, 11258061/40000000⟩
def contact3420 : RatBall := localContactBall tau3420 center3420
def work3420 : RoundedTauEval :=
  evalTau precision tau3420 contact3420 logTwoBall

theorem center_sq3420 : (center3420.re : ℝ)^2 +
    (center3420.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3420]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3420 : work3420.theta.ok = true ∧
    work3420.jac.invOK = true ∧ acceptsUnitSq work3420.out = true := by
  norm_num [work3420, contact3420, tau3420, center3420, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3420 : CellCertificate where
  tauBall := tau3420
  contactCenter := center3420
  contactBall := contact3420
  work := work3420
  center_sq := center_sq3420
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3420.1
  jac_ok := checks3420.2.1
  accepted := checks3420.2.2

def tau3421 : RatBall :=
  ⟨⟨-7/128, 49/128⟩, 3/1280⟩
def center3421 : GaussianRat :=
  ⟨-44607937/1000000000, 279044067/1000000000⟩
def contact3421 : RatBall := localContactBall tau3421 center3421
def work3421 : RoundedTauEval :=
  evalTau precision tau3421 contact3421 logTwoBall

theorem center_sq3421 : (center3421.re : ℝ)^2 +
    (center3421.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3421]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3421 : work3421.theta.ok = true ∧
    work3421.jac.invOK = true ∧ acceptsUnitSq work3421.out = true := by
  norm_num [work3421, contact3421, tau3421, center3421, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3421 : CellCertificate where
  tauBall := tau3421
  contactCenter := center3421
  contactBall := contact3421
  work := work3421
  center_sq := center_sq3421
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3421.1
  jac_ok := checks3421.2.1
  accepted := checks3421.2.2

def tau3422 : RatBall :=
  ⟨⟨-33/640, 49/128⟩, 3/1280⟩
def center3422 : GaussianRat :=
  ⟨-42068541/1000000000, 27916967/100000000⟩
def contact3422 : RatBall := localContactBall tau3422 center3422
def work3422 : RoundedTauEval :=
  evalTau precision tau3422 contact3422 logTwoBall

theorem center_sq3422 : (center3422.re : ℝ)^2 +
    (center3422.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3422]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3422 : work3422.theta.ok = true ∧
    work3422.jac.invOK = true ∧ acceptsUnitSq work3422.out = true := by
  norm_num [work3422, contact3422, tau3422, center3422, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3422 : CellCertificate where
  tauBall := tau3422
  contactCenter := center3422
  contactBall := contact3422
  work := work3422
  center_sq := center_sq3422
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3422.1
  jac_ok := checks3422.2.1
  accepted := checks3422.2.2

def tau3423 : RatBall :=
  ⟨⟨-7/128, 247/640⟩, 3/1280⟩
def center3423 : GaussianRat :=
  ⟨-2796129/62500000, 281586221/1000000000⟩
def contact3423 : RatBall := localContactBall tau3423 center3423
def work3423 : RoundedTauEval :=
  evalTau precision tau3423 contact3423 logTwoBall

theorem center_sq3423 : (center3423.re : ℝ)^2 +
    (center3423.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3423]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3423 : work3423.theta.ok = true ∧
    work3423.jac.invOK = true ∧ acceptsUnitSq work3423.out = true := by
  norm_num [work3423, contact3423, tau3423, center3423, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3423 : CellCertificate where
  tauBall := tau3423
  contactCenter := center3423
  contactBall := contact3423
  work := work3423
  center_sq := center_sq3423
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3423.1
  jac_ok := checks3423.2.1
  accepted := checks3423.2.2

def cells : List CellCertificate := [cell3416, cell3417, cell3418, cell3419, cell3420, cell3421, cell3422, cell3423]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427
