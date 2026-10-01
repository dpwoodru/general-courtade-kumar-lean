import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3432 : RatBall :=
  ⟨⟨-41/640, 251/640⟩, 3/1280⟩
def center3432 : GaussianRat :=
  ⟨-52677009/1000000000, 143127347/500000000⟩
def contact3432 : RatBall := localContactBall tau3432 center3432
def work3432 : RoundedTauEval :=
  evalTau precision tau3432 contact3432 logTwoBall

theorem center_sq3432 : (center3432.re : ℝ)^2 +
    (center3432.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3432]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3432 : work3432.theta.ok = true ∧
    work3432.jac.invOK = true ∧ acceptsUnitSq work3432.out = true := by
  norm_num [work3432, contact3432, tau3432, center3432, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3432 : CellCertificate where
  tauBall := tau3432
  contactCenter := center3432
  contactBall := contact3432
  work := work3432
  center_sq := center_sq3432
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3432.1
  jac_ok := checks3432.2.1
  accepted := checks3432.2.2

def tau3433 : RatBall :=
  ⟨⟨-9/128, 253/640⟩, 3/1280⟩
def center3433 : GaussianRat :=
  ⟨-5795507/100000000, 288479173/1000000000⟩
def contact3433 : RatBall := localContactBall tau3433 center3433
def work3433 : RoundedTauEval :=
  evalTau precision tau3433 contact3433 logTwoBall

theorem center_sq3433 : (center3433.re : ℝ)^2 +
    (center3433.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3433]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3433 : work3433.theta.ok = true ∧
    work3433.jac.invOK = true ∧ acceptsUnitSq work3433.out = true := by
  norm_num [work3433, contact3433, tau3433, center3433, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3433 : CellCertificate where
  tauBall := tau3433
  contactCenter := center3433
  contactBall := contact3433
  work := work3433
  center_sq := center_sq3433
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3433.1
  jac_ok := checks3433.2.1
  accepted := checks3433.2.2

def tau3434 : RatBall :=
  ⟨⟨-43/640, 253/640⟩, 3/1280⟩
def center3434 : GaussianRat :=
  ⟨-55396349/1000000000, 28864989/100000000⟩
def contact3434 : RatBall := localContactBall tau3434 center3434
def work3434 : RoundedTauEval :=
  evalTau precision tau3434 contact3434 logTwoBall

theorem center_sq3434 : (center3434.re : ℝ)^2 +
    (center3434.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3434]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3434 : work3434.theta.ok = true ∧
    work3434.jac.invOK = true ∧ acceptsUnitSq work3434.out = true := by
  norm_num [work3434, contact3434, tau3434, center3434, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3434 : CellCertificate where
  tauBall := tau3434
  contactCenter := center3434
  contactBall := contact3434
  work := work3434
  center_sq := center_sq3434
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3434.1
  jac_ok := checks3434.2.1
  accepted := checks3434.2.2

def tau3435 : RatBall :=
  ⟨⟨-41/640, 253/640⟩, 3/1280⟩
def center3435 : GaussianRat :=
  ⟨-52835321/1000000000, 11552523/40000000⟩
def contact3435 : RatBall := localContactBall tau3435 center3435
def work3435 : RoundedTauEval :=
  evalTau precision tau3435 contact3435 logTwoBall

theorem center_sq3435 : (center3435.re : ℝ)^2 +
    (center3435.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3435]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3435 : work3435.theta.ok = true ∧
    work3435.jac.invOK = true ∧ acceptsUnitSq work3435.out = true := by
  norm_num [work3435, contact3435, tau3435, center3435, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3435 : CellCertificate where
  tauBall := tau3435
  contactCenter := center3435
  contactBall := contact3435
  work := work3435
  center_sq := center_sq3435
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3435.1
  jac_ok := checks3435.2.1
  accepted := checks3435.2.2

def tau3436 : RatBall :=
  ⟨⟨-39/640, 249/640⟩, 3/1280⟩
def center3436 : GaussianRat :=
  ⟨-4997259/100000000, 17740947/62500000⟩
def contact3436 : RatBall := localContactBall tau3436 center3436
def work3436 : RoundedTauEval :=
  evalTau precision tau3436 contact3436 logTwoBall

theorem center_sq3436 : (center3436.re : ℝ)^2 +
    (center3436.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3436]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3436 : work3436.theta.ok = true ∧
    work3436.jac.invOK = true ∧ acceptsUnitSq work3436.out = true := by
  norm_num [work3436, contact3436, tau3436, center3436, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3436 : CellCertificate where
  tauBall := tau3436
  contactCenter := center3436
  contactBall := contact3436
  work := work3436
  center_sq := center_sq3436
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3436.1
  jac_ok := checks3436.2.1
  accepted := checks3436.2.2

def tau3437 : RatBall :=
  ⟨⟨-37/640, 249/640⟩, 3/1280⟩
def center3437 : GaussianRat :=
  ⟨-11855567/250000000, 283999143/1000000000⟩
def contact3437 : RatBall := localContactBall tau3437 center3437
def work3437 : RoundedTauEval :=
  evalTau precision tau3437 contact3437 logTwoBall

theorem center_sq3437 : (center3437.re : ℝ)^2 +
    (center3437.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3437]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3437 : work3437.theta.ok = true ∧
    work3437.jac.invOK = true ∧ acceptsUnitSq work3437.out = true := by
  norm_num [work3437, contact3437, tau3437, center3437, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3437 : CellCertificate where
  tauBall := tau3437
  contactCenter := center3437
  contactBall := contact3437
  work := work3437
  center_sq := center_sq3437
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3437.1
  jac_ok := checks3437.2.1
  accepted := checks3437.2.2

def tau3438 : RatBall :=
  ⟨⟨-39/640, 251/640⟩, 3/1280⟩
def center3438 : GaussianRat :=
  ⟨-10024261/200000000, 14320409/50000000⟩
def contact3438 : RatBall := localContactBall tau3438 center3438
def work3438 : RoundedTauEval :=
  evalTau precision tau3438 contact3438 logTwoBall

theorem center_sq3438 : (center3438.re : ℝ)^2 +
    (center3438.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3438]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3438 : work3438.theta.ok = true ∧
    work3438.jac.invOK = true ∧ acceptsUnitSq work3438.out = true := by
  norm_num [work3438, contact3438, tau3438, center3438, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3438 : CellCertificate where
  tauBall := tau3438
  contactCenter := center3438
  contactBall := contact3438
  work := work3438
  center_sq := center_sq3438
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3438.1
  jac_ok := checks3438.2.1
  accepted := checks3438.2.2

def tau3439 : RatBall :=
  ⟨⟨-37/640, 251/640⟩, 3/1280⟩
def center3439 : GaussianRat :=
  ⟨-4756353/100000000, 4477409/15625000⟩
def contact3439 : RatBall := localContactBall tau3439 center3439
def work3439 : RoundedTauEval :=
  evalTau precision tau3439 contact3439 logTwoBall

theorem center_sq3439 : (center3439.re : ℝ)^2 +
    (center3439.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3439]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3439 : work3439.theta.ok = true ∧
    work3439.jac.invOK = true ∧ acceptsUnitSq work3439.out = true := by
  norm_num [work3439, contact3439, tau3439, center3439, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3439 : CellCertificate where
  tauBall := tau3439
  contactCenter := center3439
  contactBall := contact3439
  work := work3439
  center_sq := center_sq3439
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3439.1
  jac_ok := checks3439.2.1
  accepted := checks3439.2.2

def cells : List CellCertificate := [cell3432, cell3433, cell3434, cell3435, cell3436, cell3437, cell3438, cell3439]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429
