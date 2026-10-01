import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3400 : RatBall :=
  ⟨⟨-53/640, 251/640⟩, 3/1280⟩
def center3400 : GaussianRat :=
  ⟨-67962093/1000000000, 285178227/1000000000⟩
def contact3400 : RatBall := localContactBall tau3400 center3400
def work3400 : RoundedTauEval :=
  evalTau precision tau3400 contact3400 logTwoBall

theorem center_sq3400 : (center3400.re : ℝ)^2 +
    (center3400.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3400]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3400 : work3400.theta.ok = true ∧
    work3400.jac.invOK = true ∧ acceptsUnitSq work3400.out = true := by
  norm_num [work3400, contact3400, tau3400, center3400, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3400 : CellCertificate where
  tauBall := tau3400
  contactCenter := center3400
  contactBall := contact3400
  work := work3400
  center_sq := center_sq3400
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3400.1
  jac_ok := checks3400.2.1
  accepted := checks3400.2.2

def tau3401 : RatBall :=
  ⟨⟨-51/640, 249/640⟩, 3/1280⟩
def center3401 : GaussianRat :=
  ⟨-13045627/200000000, 141418551/500000000⟩
def contact3401 : RatBall := localContactBall tau3401 center3401
def work3401 : RoundedTauEval :=
  evalTau precision tau3401 contact3401 logTwoBall

theorem center_sq3401 : (center3401.re : ℝ)^2 +
    (center3401.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3401]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3401 : work3401.theta.ok = true ∧
    work3401.jac.invOK = true ∧ acceptsUnitSq work3401.out = true := by
  norm_num [work3401, contact3401, tau3401, center3401, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3401 : CellCertificate where
  tauBall := tau3401
  contactCenter := center3401
  contactBall := contact3401
  work := work3401
  center_sq := center_sq3401
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3401.1
  jac_ok := checks3401.2.1
  accepted := checks3401.2.2

def tau3402 : RatBall :=
  ⟨⟨-49/640, 249/640⟩, 3/1280⟩
def center3402 : GaussianRat :=
  ⟨-62691561/1000000000, 141512483/500000000⟩
def contact3402 : RatBall := localContactBall tau3402 center3402
def work3402 : RoundedTauEval :=
  evalTau precision tau3402 contact3402 logTwoBall

theorem center_sq3402 : (center3402.re : ℝ)^2 +
    (center3402.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3402]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3402 : work3402.theta.ok = true ∧
    work3402.jac.invOK = true ∧ acceptsUnitSq work3402.out = true := by
  norm_num [work3402, contact3402, tau3402, center3402, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3402 : CellCertificate where
  tauBall := tau3402
  contactCenter := center3402
  contactBall := contact3402
  work := work3402
  center_sq := center_sq3402
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3402.1
  jac_ok := checks3402.2.1
  accepted := checks3402.2.2

def tau3403 : RatBall :=
  ⟨⟨-51/640, 251/640⟩, 3/1280⟩
def center3403 : GaussianRat :=
  ⟨-65420927/1000000000, 285375989/1000000000⟩
def contact3403 : RatBall := localContactBall tau3403 center3403
def work3403 : RoundedTauEval :=
  evalTau precision tau3403 contact3403 logTwoBall

theorem center_sq3403 : (center3403.re : ℝ)^2 +
    (center3403.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3403]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3403 : work3403.theta.ok = true ∧
    work3403.jac.invOK = true ∧ acceptsUnitSq work3403.out = true := by
  norm_num [work3403, contact3403, tau3403, center3403, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3403 : CellCertificate where
  tauBall := tau3403
  contactCenter := center3403
  contactBall := contact3403
  work := work3403
  center_sq := center_sq3403
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3403.1
  jac_ok := checks3403.2.1
  accepted := checks3403.2.2

def tau3404 : RatBall :=
  ⟨⟨-49/640, 251/640⟩, 3/1280⟩
def center3404 : GaussianRat :=
  ⟨-6287709/100000000, 142783229/500000000⟩
def contact3404 : RatBall := localContactBall tau3404 center3404
def work3404 : RoundedTauEval :=
  evalTau precision tau3404 contact3404 logTwoBall

theorem center_sq3404 : (center3404.re : ℝ)^2 +
    (center3404.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3404]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3404 : work3404.theta.ok = true ∧
    work3404.jac.invOK = true ∧ acceptsUnitSq work3404.out = true := by
  norm_num [work3404, contact3404, tau3404, center3404, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3404 : CellCertificate where
  tauBall := tau3404
  contactCenter := center3404
  contactBall := contact3404
  work := work3404
  center_sq := center_sq3404
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3404.1
  jac_ok := checks3404.2.1
  accepted := checks3404.2.2

def tau3405 : RatBall :=
  ⟨⟨-47/640, 241/640⟩, 3/1280⟩
def center3405 : GaussianRat :=
  ⟨-59463601/1000000000, 273101301/1000000000⟩
def contact3405 : RatBall := localContactBall tau3405 center3405
def work3405 : RoundedTauEval :=
  evalTau precision tau3405 contact3405 logTwoBall

theorem center_sq3405 : (center3405.re : ℝ)^2 +
    (center3405.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3405]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3405 : work3405.theta.ok = true ∧
    work3405.jac.invOK = true ∧ acceptsUnitSq work3405.out = true := by
  norm_num [work3405, contact3405, tau3405, center3405, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3405 : CellCertificate where
  tauBall := tau3405
  contactCenter := center3405
  contactBall := contact3405
  work := work3405
  center_sq := center_sq3405
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3405.1
  jac_ok := checks3405.2.1
  accepted := checks3405.2.2

def tau3406 : RatBall :=
  ⟨⟨-9/128, 241/640⟩, 3/1280⟩
def center3406 : GaussianRat :=
  ⟨-11390081/200000000, 136632679/500000000⟩
def contact3406 : RatBall := localContactBall tau3406 center3406
def work3406 : RoundedTauEval :=
  evalTau precision tau3406 contact3406 logTwoBall

theorem center_sq3406 : (center3406.re : ℝ)^2 +
    (center3406.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3406]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3406 : work3406.theta.ok = true ∧
    work3406.jac.invOK = true ∧ acceptsUnitSq work3406.out = true := by
  norm_num [work3406, contact3406, tau3406, center3406, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3406 : CellCertificate where
  tauBall := tau3406
  contactCenter := center3406
  contactBall := contact3406
  work := work3406
  center_sq := center_sq3406
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3406.1
  jac_ok := checks3406.2.1
  accepted := checks3406.2.2

def tau3407 : RatBall :=
  ⟨⟨-47/640, 243/640⟩, 3/1280⟩
def center3407 : GaussianRat :=
  ⟨-59632267/1000000000, 137808407/500000000⟩
def contact3407 : RatBall := localContactBall tau3407 center3407
def work3407 : RoundedTauEval :=
  evalTau precision tau3407 contact3407 logTwoBall

theorem center_sq3407 : (center3407.re : ℝ)^2 +
    (center3407.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3407]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3407 : work3407.theta.ok = true ∧
    work3407.jac.invOK = true ∧ acceptsUnitSq work3407.out = true := by
  norm_num [work3407, contact3407, tau3407, center3407, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3407 : CellCertificate where
  tauBall := tau3407
  contactCenter := center3407
  contactBall := contact3407
  work := work3407
  center_sq := center_sq3407
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3407.1
  jac_ok := checks3407.2.1
  accepted := checks3407.2.2

def cells : List CellCertificate := [cell3400, cell3401, cell3402, cell3403, cell3404, cell3405, cell3406, cell3407]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425
