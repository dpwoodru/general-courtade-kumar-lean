import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3376 : RatBall :=
  ⟨⟨-57/640, 247/640⟩, 3/1280⟩
def center3376 : GaussianRat :=
  ⟨-72610227/1000000000, 34963383/125000000⟩
def contact3376 : RatBall := localContactBall tau3376 center3376
def work3376 : RoundedTauEval :=
  evalTau precision tau3376 contact3376 logTwoBall

theorem center_sq3376 : (center3376.re : ℝ)^2 +
    (center3376.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3376]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3376 : work3376.theta.ok = true ∧
    work3376.jac.invOK = true ∧ acceptsUnitSq work3376.out = true := by
  norm_num [work3376, contact3376, tau3376, center3376, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3376 : CellCertificate where
  tauBall := tau3376
  contactCenter := center3376
  contactBall := contact3376
  work := work3376
  center_sq := center_sq3376
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3376.1
  jac_ok := checks3376.2.1
  accepted := checks3376.2.2

def tau3377 : RatBall :=
  ⟨⟨-11/128, 241/640⟩, 3/1280⟩
def center3377 : GaussianRat :=
  ⟨-34746169/500000000, 68094139/250000000⟩
def contact3377 : RatBall := localContactBall tau3377 center3377
def work3377 : RoundedTauEval :=
  evalTau precision tau3377 contact3377 logTwoBall

theorem center_sq3377 : (center3377.re : ℝ)^2 +
    (center3377.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3377]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3377 : work3377.theta.ok = true ∧
    work3377.jac.invOK = true ∧ acceptsUnitSq work3377.out = true := by
  norm_num [work3377, contact3377, tau3377, center3377, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3377 : CellCertificate where
  tauBall := tau3377
  contactCenter := center3377
  contactBall := contact3377
  work := work3377
  center_sq := center_sq3377
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3377.1
  jac_ok := checks3377.2.1
  accepted := checks3377.2.2

def tau3378 : RatBall :=
  ⟨⟨-53/640, 241/640⟩, 3/1280⟩
def center3378 : GaussianRat :=
  ⟨-13397789/200000000, 54513591/200000000⟩
def contact3378 : RatBall := localContactBall tau3378 center3378
def work3378 : RoundedTauEval :=
  evalTau precision tau3378 contact3378 logTwoBall

theorem center_sq3378 : (center3378.re : ℝ)^2 +
    (center3378.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3378]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3378 : work3378.theta.ok = true ∧
    work3378.jac.invOK = true ∧ acceptsUnitSq work3378.out = true := by
  norm_num [work3378, contact3378, tau3378, center3378, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3378 : CellCertificate where
  tauBall := tau3378
  contactCenter := center3378
  contactBall := contact3378
  work := work3378
  center_sq := center_sq3378
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3378.1
  jac_ok := checks3378.2.1
  accepted := checks3378.2.2

def tau3379 : RatBall :=
  ⟨⟨-11/128, 243/640⟩, 3/1280⟩
def center3379 : GaussianRat :=
  ⟨-13937693/200000000, 54976403/200000000⟩
def contact3379 : RatBall := localContactBall tau3379 center3379
def work3379 : RoundedTauEval :=
  evalTau precision tau3379 contact3379 logTwoBall

theorem center_sq3379 : (center3379.re : ℝ)^2 +
    (center3379.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3379]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3379 : work3379.theta.ok = true ∧
    work3379.jac.invOK = true ∧ acceptsUnitSq work3379.out = true := by
  norm_num [work3379, contact3379, tau3379, center3379, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3379 : CellCertificate where
  tauBall := tau3379
  contactCenter := center3379
  contactBall := contact3379
  work := work3379
  center_sq := center_sq3379
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3379.1
  jac_ok := checks3379.2.1
  accepted := checks3379.2.2

def tau3380 : RatBall :=
  ⟨⟨-53/640, 243/640⟩, 3/1280⟩
def center3380 : GaussianRat :=
  ⟨-67178257/1000000000, 137538033/500000000⟩
def contact3380 : RatBall := localContactBall tau3380 center3380
def work3380 : RoundedTauEval :=
  evalTau precision tau3380 contact3380 logTwoBall

theorem center_sq3380 : (center3380.re : ℝ)^2 +
    (center3380.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3380]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3380 : work3380.theta.ok = true ∧
    work3380.jac.invOK = true ∧ acceptsUnitSq work3380.out = true := by
  norm_num [work3380, contact3380, tau3380, center3380, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3380 : CellCertificate where
  tauBall := tau3380
  contactCenter := center3380
  contactBall := contact3380
  work := work3380
  center_sq := center_sq3380
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3380.1
  jac_ok := checks3380.2.1
  accepted := checks3380.2.2

def tau3381 : RatBall :=
  ⟨⟨-51/640, 241/640⟩, 3/1280⟩
def center3381 : GaussianRat :=
  ⟨-16120741/250000000, 34094071/125000000⟩
def contact3381 : RatBall := localContactBall tau3381 center3381
def work3381 : RoundedTauEval :=
  evalTau precision tau3381 contact3381 logTwoBall

theorem center_sq3381 : (center3381.re : ℝ)^2 +
    (center3381.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3381]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3381 : work3381.theta.ok = true ∧
    work3381.jac.invOK = true ∧ acceptsUnitSq work3381.out = true := by
  norm_num [work3381, contact3381, tau3381, center3381, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3381 : CellCertificate where
  tauBall := tau3381
  contactCenter := center3381
  contactBall := contact3381
  work := work3381
  center_sq := center_sq3381
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3381.1
  jac_ok := checks3381.2.1
  accepted := checks3381.2.2

def tau3382 : RatBall :=
  ⟨⟨-49/640, 241/640⟩, 3/1280⟩
def center3382 : GaussianRat :=
  ⟨-12394897/200000000, 272930361/1000000000⟩
def contact3382 : RatBall := localContactBall tau3382 center3382
def work3382 : RoundedTauEval :=
  evalTau precision tau3382 contact3382 logTwoBall

theorem center_sq3382 : (center3382.re : ℝ)^2 +
    (center3382.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3382]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3382 : work3382.theta.ok = true ∧
    work3382.jac.invOK = true ∧ acceptsUnitSq work3382.out = true := by
  norm_num [work3382, contact3382, tau3382, center3382, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3382 : CellCertificate where
  tauBall := tau3382
  contactCenter := center3382
  contactBall := contact3382
  work := work3382
  center_sq := center_sq3382
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3382.1
  jac_ok := checks3382.2.1
  accepted := checks3382.2.2

def tau3383 : RatBall :=
  ⟨⟨-51/640, 243/640⟩, 3/1280⟩
def center3383 : GaussianRat :=
  ⟨-32332713/500000000, 275263239/1000000000⟩
def contact3383 : RatBall := localContactBall tau3383 center3383
def work3383 : RoundedTauEval :=
  evalTau precision tau3383 contact3383 logTwoBall

theorem center_sq3383 : (center3383.re : ℝ)^2 +
    (center3383.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3383]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3383 : work3383.theta.ok = true ∧
    work3383.jac.invOK = true ∧ acceptsUnitSq work3383.out = true := by
  norm_num [work3383, contact3383, tau3383, center3383, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3383 : CellCertificate where
  tauBall := tau3383
  contactCenter := center3383
  contactBall := contact3383
  work := work3383
  center_sq := center_sq3383
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3383.1
  jac_ok := checks3383.2.1
  accepted := checks3383.2.2

def cells : List CellCertificate := [cell3376, cell3377, cell3378, cell3379, cell3380, cell3381, cell3382, cell3383]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422
