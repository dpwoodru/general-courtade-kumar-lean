import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3456 : RatBall :=
  ⟨⟨-23/640, 49/128⟩, 3/1280⟩
def center3456 : GaussianRat :=
  ⟨-7337051/250000000, 279688291/1000000000⟩
def contact3456 : RatBall := localContactBall tau3456 center3456
def work3456 : RoundedTauEval :=
  evalTau precision tau3456 contact3456 logTwoBall

theorem center_sq3456 : (center3456.re : ℝ)^2 +
    (center3456.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3456]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3456 : work3456.theta.ok = true ∧
    work3456.jac.invOK = true ∧ acceptsUnitSq work3456.out = true := by
  norm_num [work3456, contact3456, tau3456, center3456, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3456 : CellCertificate where
  tauBall := tau3456
  contactCenter := center3456
  contactBall := contact3456
  work := work3456
  center_sq := center_sq3456
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3456.1
  jac_ok := checks3456.2.1
  accepted := checks3456.2.2

def tau3457 : RatBall :=
  ⟨⟨-21/640, 49/128⟩, 3/1280⟩
def center3457 : GaussianRat :=
  ⟨-6700043/250000000, 139884999/500000000⟩
def contact3457 : RatBall := localContactBall tau3457 center3457
def work3457 : RoundedTauEval :=
  evalTau precision tau3457 contact3457 logTwoBall

theorem center_sq3457 : (center3457.re : ℝ)^2 +
    (center3457.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3457]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3457 : work3457.theta.ok = true ∧
    work3457.jac.invOK = true ∧ acceptsUnitSq work3457.out = true := by
  norm_num [work3457, contact3457, tau3457, center3457, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3457 : CellCertificate where
  tauBall := tau3457
  contactCenter := center3457
  contactBall := contact3457
  work := work3457
  center_sq := center_sq3457
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3457.1
  jac_ok := checks3457.2.1
  accepted := checks3457.2.2

def tau3458 : RatBall :=
  ⟨⟨-23/640, 247/640⟩, 3/1280⟩
def center3458 : GaussianRat :=
  ⟨-1839637/62500000, 141119723/500000000⟩
def contact3458 : RatBall := localContactBall tau3458 center3458
def work3458 : RoundedTauEval :=
  evalTau precision tau3458 contact3458 logTwoBall

theorem center_sq3458 : (center3458.re : ℝ)^2 +
    (center3458.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3458]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3458 : work3458.theta.ok = true ∧
    work3458.jac.invOK = true ∧ acceptsUnitSq work3458.out = true := by
  norm_num [work3458, contact3458, tau3458, center3458, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3458 : CellCertificate where
  tauBall := tau3458
  contactCenter := center3458
  contactBall := contact3458
  work := work3458
  center_sq := center_sq3458
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3458.1
  jac_ok := checks3458.2.1
  accepted := checks3458.2.2

def tau3459 : RatBall :=
  ⟨⟨-21/640, 247/640⟩, 3/1280⟩
def center3459 : GaussianRat :=
  ⟨-26878737/1000000000, 282322297/1000000000⟩
def contact3459 : RatBall := localContactBall tau3459 center3459
def work3459 : RoundedTauEval :=
  evalTau precision tau3459 contact3459 logTwoBall

theorem center_sq3459 : (center3459.re : ℝ)^2 +
    (center3459.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3459]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3459 : work3459.theta.ok = true ∧
    work3459.jac.invOK = true ∧ acceptsUnitSq work3459.out = true := by
  norm_num [work3459, contact3459, tau3459, center3459, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3459 : CellCertificate where
  tauBall := tau3459
  contactCenter := center3459
  contactBall := contact3459
  work := work3459
  center_sq := center_sq3459
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3459.1
  jac_ok := checks3459.2.1
  accepted := checks3459.2.2

def tau3460 : RatBall :=
  ⟨⟨-31/640, 249/640⟩, 3/1280⟩
def center3460 : GaussianRat :=
  ⟨-19880031/500000000, 56877303/200000000⟩
def contact3460 : RatBall := localContactBall tau3460 center3460
def work3460 : RoundedTauEval :=
  evalTau precision tau3460 contact3460 logTwoBall

theorem center_sq3460 : (center3460.re : ℝ)^2 +
    (center3460.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3460 : work3460.theta.ok = true ∧
    work3460.jac.invOK = true ∧ acceptsUnitSq work3460.out = true := by
  norm_num [work3460, contact3460, tau3460, center3460, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3460 : CellCertificate where
  tauBall := tau3460
  contactCenter := center3460
  contactBall := contact3460
  work := work3460
  center_sq := center_sq3460
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3460.1
  jac_ok := checks3460.2.1
  accepted := checks3460.2.2

def tau3461 : RatBall :=
  ⟨⟨-29/640, 249/640⟩, 3/1280⟩
def center3461 : GaussianRat :=
  ⟨-37202587/1000000000, 284500691/1000000000⟩
def contact3461 : RatBall := localContactBall tau3461 center3461
def work3461 : RoundedTauEval :=
  evalTau precision tau3461 contact3461 logTwoBall

theorem center_sq3461 : (center3461.re : ℝ)^2 +
    (center3461.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3461]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3461 : work3461.theta.ok = true ∧
    work3461.jac.invOK = true ∧ acceptsUnitSq work3461.out = true := by
  norm_num [work3461, contact3461, tau3461, center3461, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3461 : CellCertificate where
  tauBall := tau3461
  contactCenter := center3461
  contactBall := contact3461
  work := work3461
  center_sq := center_sq3461
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3461.1
  jac_ok := checks3461.2.1
  accepted := checks3461.2.2

def tau3462 : RatBall :=
  ⟨⟨-31/640, 251/640⟩, 3/1280⟩
def center3462 : GaussianRat :=
  ⟨-4984851/125000000, 286946953/1000000000⟩
def contact3462 : RatBall := localContactBall tau3462 center3462
def work3462 : RoundedTauEval :=
  evalTau precision tau3462 contact3462 logTwoBall

theorem center_sq3462 : (center3462.re : ℝ)^2 +
    (center3462.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3462]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3462 : work3462.theta.ok = true ∧
    work3462.jac.invOK = true ∧ acceptsUnitSq work3462.out = true := by
  norm_num [work3462, contact3462, tau3462, center3462, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3462 : CellCertificate where
  tauBall := tau3462
  contactCenter := center3462
  contactBall := contact3462
  work := work3462
  center_sq := center_sq3462
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3462.1
  jac_ok := checks3462.2.1
  accepted := checks3462.2.2

def tau3463 : RatBall :=
  ⟨⟨-29/640, 251/640⟩, 3/1280⟩
def center3463 : GaussianRat :=
  ⟨-1865689/50000000, 287062723/1000000000⟩
def contact3463 : RatBall := localContactBall tau3463 center3463
def work3463 : RoundedTauEval :=
  evalTau precision tau3463 contact3463 logTwoBall

theorem center_sq3463 : (center3463.re : ℝ)^2 +
    (center3463.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3463]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3463 : work3463.theta.ok = true ∧
    work3463.jac.invOK = true ∧ acceptsUnitSq work3463.out = true := by
  norm_num [work3463, contact3463, tau3463, center3463, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3463 : CellCertificate where
  tauBall := tau3463
  contactCenter := center3463
  contactBall := contact3463
  work := work3463
  center_sq := center_sq3463
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3463.1
  jac_ok := checks3463.2.1
  accepted := checks3463.2.2

def cells : List CellCertificate := [cell3456, cell3457, cell3458, cell3459, cell3460, cell3461, cell3462, cell3463]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432
