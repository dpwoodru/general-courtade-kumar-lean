import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3272 : RatBall :=
  ⟨⟨-97/640, 47/128⟩, 3/1280⟩
def center3272 : GaussianRat :=
  ⟨-15043717/125000000, 259604029/1000000000⟩
def contact3272 : RatBall := localContactBall tau3272 center3272
def work3272 : RoundedTauEval :=
  evalTau precision tau3272 contact3272 logTwoBall

theorem center_sq3272 : (center3272.re : ℝ)^2 +
    (center3272.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3272]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3272 : work3272.theta.ok = true ∧
    work3272.jac.invOK = true ∧ acceptsUnitSq work3272.out = true := by
  norm_num [work3272, contact3272, tau3272, center3272, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3272 : CellCertificate where
  tauBall := tau3272
  contactCenter := center3272
  contactBall := contact3272
  work := work3272
  center_sq := center_sq3272
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3272.1
  jac_ok := checks3272.2.1
  accepted := checks3272.2.2

def tau3273 : RatBall :=
  ⟨⟨-99/640, 237/640⟩, 3/1280⟩
def center3273 : GaussianRat :=
  ⟨-123079793/1000000000, 65423867/250000000⟩
def contact3273 : RatBall := localContactBall tau3273 center3273
def work3273 : RoundedTauEval :=
  evalTau precision tau3273 contact3273 logTwoBall

theorem center_sq3273 : (center3273.re : ℝ)^2 +
    (center3273.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3273]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3273 : work3273.theta.ok = true ∧
    work3273.jac.invOK = true ∧ acceptsUnitSq work3273.out = true := by
  norm_num [work3273, contact3273, tau3273, center3273, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3273 : CellCertificate where
  tauBall := tau3273
  contactCenter := center3273
  contactBall := contact3273
  work := work3273
  center_sq := center_sq3273
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3273.1
  jac_ok := checks3273.2.1
  accepted := checks3273.2.2

def tau3274 : RatBall :=
  ⟨⟨-97/640, 237/640⟩, 3/1280⟩
def center3274 : GaussianRat :=
  ⟨-60333117/500000000, 6550423/25000000⟩
def contact3274 : RatBall := localContactBall tau3274 center3274
def work3274 : RoundedTauEval :=
  evalTau precision tau3274 contact3274 logTwoBall

theorem center_sq3274 : (center3274.re : ℝ)^2 +
    (center3274.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3274]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3274 : work3274.theta.ok = true ∧
    work3274.jac.invOK = true ∧ acceptsUnitSq work3274.out = true := by
  norm_num [work3274, contact3274, tau3274, center3274, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3274 : CellCertificate where
  tauBall := tau3274
  contactCenter := center3274
  contactBall := contact3274
  work := work3274
  center_sq := center_sq3274
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3274.1
  jac_ok := checks3274.2.1
  accepted := checks3274.2.2

def tau3275 : RatBall :=
  ⟨⟨-19/128, 229/640⟩, 3/1280⟩
def center3275 : GaussianRat :=
  ⟨-117029769/1000000000, 63174463/250000000⟩
def contact3275 : RatBall := localContactBall tau3275 center3275
def work3275 : RoundedTauEval :=
  evalTau precision tau3275 contact3275 logTwoBall

theorem center_sq3275 : (center3275.re : ℝ)^2 +
    (center3275.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3275]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3275 : work3275.theta.ok = true ∧
    work3275.jac.invOK = true ∧ acceptsUnitSq work3275.out = true := by
  norm_num [work3275, contact3275, tau3275, center3275, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3275 : CellCertificate where
  tauBall := tau3275
  contactCenter := center3275
  contactBall := contact3275
  work := work3275
  center_sq := center_sq3275
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3275.1
  jac_ok := checks3275.2.1
  accepted := checks3275.2.2

def tau3276 : RatBall :=
  ⟨⟨-93/640, 229/640⟩, 3/1280⟩
def center3276 : GaussianRat :=
  ⟨-28657529/250000000, 252991629/1000000000⟩
def contact3276 : RatBall := localContactBall tau3276 center3276
def work3276 : RoundedTauEval :=
  evalTau precision tau3276 contact3276 logTwoBall

theorem center_sq3276 : (center3276.re : ℝ)^2 +
    (center3276.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3276]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3276 : work3276.theta.ok = true ∧
    work3276.jac.invOK = true ∧ acceptsUnitSq work3276.out = true := by
  norm_num [work3276, contact3276, tau3276, center3276, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3276 : CellCertificate where
  tauBall := tau3276
  contactCenter := center3276
  contactBall := contact3276
  work := work3276
  center_sq := center_sq3276
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3276.1
  jac_ok := checks3276.2.1
  accepted := checks3276.2.2

def tau3277 : RatBall :=
  ⟨⟨-19/128, 231/640⟩, 3/1280⟩
def center3277 : GaussianRat :=
  ⟨-117328287/1000000000, 255098241/1000000000⟩
def contact3277 : RatBall := localContactBall tau3277 center3277
def work3277 : RoundedTauEval :=
  evalTau precision tau3277 contact3277 logTwoBall

theorem center_sq3277 : (center3277.re : ℝ)^2 +
    (center3277.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3277]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3277 : work3277.theta.ok = true ∧
    work3277.jac.invOK = true ∧ acceptsUnitSq work3277.out = true := by
  norm_num [work3277, contact3277, tau3277, center3277, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3277 : CellCertificate where
  tauBall := tau3277
  contactCenter := center3277
  contactBall := contact3277
  work := work3277
  center_sq := center_sq3277
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3277.1
  jac_ok := checks3277.2.1
  accepted := checks3277.2.2

def tau3278 : RatBall :=
  ⟨⟨-93/640, 231/640⟩, 3/1280⟩
def center3278 : GaussianRat :=
  ⟨-114923139/1000000000, 12769801/50000000⟩
def contact3278 : RatBall := localContactBall tau3278 center3278
def work3278 : RoundedTauEval :=
  evalTau precision tau3278 contact3278 logTwoBall

theorem center_sq3278 : (center3278.re : ℝ)^2 +
    (center3278.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3278]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3278 : work3278.theta.ok = true ∧
    work3278.jac.invOK = true ∧ acceptsUnitSq work3278.out = true := by
  norm_num [work3278, contact3278, tau3278, center3278, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3278 : CellCertificate where
  tauBall := tau3278
  contactCenter := center3278
  contactBall := contact3278
  work := work3278
  center_sq := center_sq3278
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3278.1
  jac_ok := checks3278.2.1
  accepted := checks3278.2.2

def tau3279 : RatBall :=
  ⟨⟨-19/128, 233/640⟩, 3/1280⟩
def center3279 : GaussianRat :=
  ⟨-7351929/62500000, 128752067/500000000⟩
def contact3279 : RatBall := localContactBall tau3279 center3279
def work3279 : RoundedTauEval :=
  evalTau precision tau3279 contact3279 logTwoBall

theorem center_sq3279 : (center3279.re : ℝ)^2 +
    (center3279.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3279]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3279 : work3279.theta.ok = true ∧
    work3279.jac.invOK = true ∧ acceptsUnitSq work3279.out = true := by
  norm_num [work3279, contact3279, tau3279, center3279, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3279 : CellCertificate where
  tauBall := tau3279
  contactCenter := center3279
  contactBall := contact3279
  work := work3279
  center_sq := center_sq3279
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3279.1
  jac_ok := checks3279.2.1
  accepted := checks3279.2.2

def cells : List CellCertificate := [cell3272, cell3273, cell3274, cell3275, cell3276, cell3277, cell3278, cell3279]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409
