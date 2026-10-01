import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3232 : RatBall :=
  ⟨⟨-119/640, 227/640⟩, 3/1280⟩
def center3232 : GaussianRat :=
  ⟨-145138173/1000000000, 123210011/500000000⟩
def contact3232 : RatBall := localContactBall tau3232 center3232
def work3232 : RoundedTauEval :=
  evalTau precision tau3232 contact3232 logTwoBall

theorem center_sq3232 : (center3232.re : ℝ)^2 +
    (center3232.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3232]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3232 : work3232.theta.ok = true ∧
    work3232.jac.invOK = true ∧ acceptsUnitSq work3232.out = true := by
  norm_num [work3232, contact3232, tau3232, center3232, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3232 : CellCertificate where
  tauBall := tau3232
  contactCenter := center3232
  contactBall := contact3232
  work := work3232
  center_sq := center_sq3232
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3232.1
  jac_ok := checks3232.2.1
  accepted := checks3232.2.2

def tau3233 : RatBall :=
  ⟨⟨-117/640, 227/640⟩, 3/1280⟩
def center3233 : GaussianRat :=
  ⟨-142795751/1000000000, 246771071/1000000000⟩
def contact3233 : RatBall := localContactBall tau3233 center3233
def work3233 : RoundedTauEval :=
  evalTau precision tau3233 contact3233 logTwoBall

theorem center_sq3233 : (center3233.re : ℝ)^2 +
    (center3233.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3233]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3233 : work3233.theta.ok = true ∧
    work3233.jac.invOK = true ∧ acceptsUnitSq work3233.out = true := by
  norm_num [work3233, contact3233, tau3233, center3233, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3233 : CellCertificate where
  tauBall := tau3233
  contactCenter := center3233
  contactBall := contact3233
  work := work3233
  center_sq := center_sq3233
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3233.1
  jac_ok := checks3233.2.1
  accepted := checks3233.2.2

def tau3234 : RatBall :=
  ⟨⟨-23/128, 45/128⟩, 3/1280⟩
def center3234 : GaussianRat :=
  ⟨-5604287/40000000, 122385171/500000000⟩
def contact3234 : RatBall := localContactBall tau3234 center3234
def work3234 : RoundedTauEval :=
  evalTau precision tau3234 contact3234 logTwoBall

theorem center_sq3234 : (center3234.re : ℝ)^2 +
    (center3234.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3234]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3234 : work3234.theta.ok = true ∧
    work3234.jac.invOK = true ∧ acceptsUnitSq work3234.out = true := by
  norm_num [work3234, contact3234, tau3234, center3234, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3234 : CellCertificate where
  tauBall := tau3234
  contactCenter := center3234
  contactBall := contact3234
  work := work3234
  center_sq := center_sq3234
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3234.1
  jac_ok := checks3234.2.1
  accepted := checks3234.2.2

def tau3235 : RatBall :=
  ⟨⟨-113/640, 45/128⟩, 3/1280⟩
def center3235 : GaussianRat :=
  ⟨-137760383/1000000000, 245107147/1000000000⟩
def contact3235 : RatBall := localContactBall tau3235 center3235
def work3235 : RoundedTauEval :=
  evalTau precision tau3235 contact3235 logTwoBall

theorem center_sq3235 : (center3235.re : ℝ)^2 +
    (center3235.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3235]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3235 : work3235.theta.ok = true ∧
    work3235.jac.invOK = true ∧ acceptsUnitSq work3235.out = true := by
  norm_num [work3235, contact3235, tau3235, center3235, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3235 : CellCertificate where
  tauBall := tau3235
  contactCenter := center3235
  contactBall := contact3235
  work := work3235
  center_sq := center_sq3235
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3235.1
  jac_ok := checks3235.2.1
  accepted := checks3235.2.2

def tau3236 : RatBall :=
  ⟨⟨-23/128, 227/640⟩, 3/1280⟩
def center3236 : GaussianRat :=
  ⟨-140448677/1000000000, 247117293/1000000000⟩
def contact3236 : RatBall := localContactBall tau3236 center3236
def work3236 : RoundedTauEval :=
  evalTau precision tau3236 contact3236 logTwoBall

theorem center_sq3236 : (center3236.re : ℝ)^2 +
    (center3236.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3236]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3236 : work3236.theta.ok = true ∧
    work3236.jac.invOK = true ∧ acceptsUnitSq work3236.out = true := by
  norm_num [work3236, contact3236, tau3236, center3236, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3236 : CellCertificate where
  tauBall := tau3236
  contactCenter := center3236
  contactBall := contact3236
  work := work3236
  center_sq := center_sq3236
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3236.1
  jac_ok := checks3236.2.1
  accepted := checks3236.2.2

def tau3237 : RatBall :=
  ⟨⟨-113/640, 227/640⟩, 3/1280⟩
def center3237 : GaussianRat :=
  ⟨-138097011/1000000000, 61864659/250000000⟩
def contact3237 : RatBall := localContactBall tau3237 center3237
def work3237 : RoundedTauEval :=
  evalTau precision tau3237 contact3237 logTwoBall

theorem center_sq3237 : (center3237.re : ℝ)^2 +
    (center3237.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3237]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3237 : work3237.theta.ok = true ∧
    work3237.jac.invOK = true ∧ acceptsUnitSq work3237.out = true := by
  norm_num [work3237, contact3237, tau3237, center3237, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3237 : CellCertificate where
  tauBall := tau3237
  contactCenter := center3237
  contactBall := contact3237
  work := work3237
  center_sq := center_sq3237
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3237.1
  jac_ok := checks3237.2.1
  accepted := checks3237.2.2

def tau3238 : RatBall :=
  ⟨⟨-117/640, 229/640⟩, 3/1280⟩
def center3238 : GaussianRat :=
  ⟨-143146729/1000000000, 249118251/1000000000⟩
def contact3238 : RatBall := localContactBall tau3238 center3238
def work3238 : RoundedTauEval :=
  evalTau precision tau3238 contact3238 logTwoBall

theorem center_sq3238 : (center3238.re : ℝ)^2 +
    (center3238.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3238]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3238 : work3238.theta.ok = true ∧
    work3238.jac.invOK = true ∧ acceptsUnitSq work3238.out = true := by
  norm_num [work3238, contact3238, tau3238, center3238, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3238 : CellCertificate where
  tauBall := tau3238
  contactCenter := center3238
  contactBall := contact3238
  work := work3238
  center_sq := center_sq3238
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3238.1
  jac_ok := checks3238.2.1
  accepted := checks3238.2.2

def tau3239 : RatBall :=
  ⟨⟨-23/128, 229/640⟩, 3/1280⟩
def center3239 : GaussianRat :=
  ⟨-70397387/500000000, 249469121/1000000000⟩
def contact3239 : RatBall := localContactBall tau3239 center3239
def work3239 : RoundedTauEval :=
  evalTau precision tau3239 contact3239 logTwoBall

theorem center_sq3239 : (center3239.re : ℝ)^2 +
    (center3239.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3239]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3239 : work3239.theta.ok = true ∧
    work3239.jac.invOK = true ∧ acceptsUnitSq work3239.out = true := by
  norm_num [work3239, contact3239, tau3239, center3239, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3239 : CellCertificate where
  tauBall := tau3239
  contactCenter := center3239
  contactBall := contact3239
  work := work3239
  center_sq := center_sq3239
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3239.1
  jac_ok := checks3239.2.1
  accepted := checks3239.2.2

def cells : List CellCertificate := [cell3232, cell3233, cell3234, cell3235, cell3236, cell3237, cell3238, cell3239]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404
