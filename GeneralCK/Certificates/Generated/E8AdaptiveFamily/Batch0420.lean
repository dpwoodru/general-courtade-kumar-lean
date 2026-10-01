import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3360 : RatBall :=
  ⟨⟨-13/128, 247/640⟩, 3/1280⟩
def center3360 : GaussianRat :=
  ⟨-82665793/1000000000, 278811601/1000000000⟩
def contact3360 : RatBall := localContactBall tau3360 center3360
def work3360 : RoundedTauEval :=
  evalTau precision tau3360 contact3360 logTwoBall

theorem center_sq3360 : (center3360.re : ℝ)^2 +
    (center3360.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3360]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3360 : work3360.theta.ok = true ∧
    work3360.jac.invOK = true ∧ acceptsUnitSq work3360.out = true := by
  norm_num [work3360, contact3360, tau3360, center3360, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3360 : CellCertificate where
  tauBall := tau3360
  contactCenter := center3360
  contactBall := contact3360
  work := work3360
  center_sq := center_sq3360
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3360.1
  jac_ok := checks3360.2.1
  accepted := checks3360.2.2

def tau3361 : RatBall :=
  ⟨⟨-63/640, 241/640⟩, 3/1280⟩
def center3361 : GaussianRat :=
  ⟨-15895643/200000000, 271543799/1000000000⟩
def contact3361 : RatBall := localContactBall tau3361 center3361
def work3361 : RoundedTauEval :=
  evalTau precision tau3361 contact3361 logTwoBall

theorem center_sq3361 : (center3361.re : ℝ)^2 +
    (center3361.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3361]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3361 : work3361.theta.ok = true ∧
    work3361.jac.invOK = true ∧ acceptsUnitSq work3361.out = true := by
  norm_num [work3361, contact3361, tau3361, center3361, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3361 : CellCertificate where
  tauBall := tau3361
  contactCenter := center3361
  contactBall := contact3361
  work := work3361
  center_sq := center_sq3361
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3361.1
  jac_ok := checks3361.2.1
  accepted := checks3361.2.2

def tau3362 : RatBall :=
  ⟨⟨-61/640, 241/640⟩, 3/1280⟩
def center3362 : GaussianRat :=
  ⟨-38493039/500000000, 67940497/250000000⟩
def contact3362 : RatBall := localContactBall tau3362 center3362
def work3362 : RoundedTauEval :=
  evalTau precision tau3362 contact3362 logTwoBall

theorem center_sq3362 : (center3362.re : ℝ)^2 +
    (center3362.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3362]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3362 : work3362.theta.ok = true ∧
    work3362.jac.invOK = true ∧ acceptsUnitSq work3362.out = true := by
  norm_num [work3362, contact3362, tau3362, center3362, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3362 : CellCertificate where
  tauBall := tau3362
  contactCenter := center3362
  contactBall := contact3362
  work := work3362
  center_sq := center_sq3362
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3362.1
  jac_ok := checks3362.2.1
  accepted := checks3362.2.2

def tau3363 : RatBall :=
  ⟨⟨-63/640, 243/640⟩, 3/1280⟩
def center3363 : GaussianRat :=
  ⟨-79701237/1000000000, 274037749/1000000000⟩
def contact3363 : RatBall := localContactBall tau3363 center3363
def work3363 : RoundedTauEval :=
  evalTau precision tau3363 contact3363 logTwoBall

theorem center_sq3363 : (center3363.re : ℝ)^2 +
    (center3363.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3363]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3363 : work3363.theta.ok = true ∧
    work3363.jac.invOK = true ∧ acceptsUnitSq work3363.out = true := by
  norm_num [work3363, contact3363, tau3363, center3363, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3363 : CellCertificate where
  tauBall := tau3363
  contactCenter := center3363
  contactBall := contact3363
  work := work3363
  center_sq := center_sq3363
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3363.1
  jac_ok := checks3363.2.1
  accepted := checks3363.2.2

def tau3364 : RatBall :=
  ⟨⟨-61/640, 243/640⟩, 3/1280⟩
def center3364 : GaussianRat :=
  ⟨-77202433/1000000000, 5485179/20000000⟩
def contact3364 : RatBall := localContactBall tau3364 center3364
def work3364 : RoundedTauEval :=
  evalTau precision tau3364 contact3364 logTwoBall

theorem center_sq3364 : (center3364.re : ℝ)^2 +
    (center3364.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3364]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3364 : work3364.theta.ok = true ∧
    work3364.jac.invOK = true ∧ acceptsUnitSq work3364.out = true := by
  norm_num [work3364, contact3364, tau3364, center3364, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3364 : CellCertificate where
  tauBall := tau3364
  contactCenter := center3364
  contactBall := contact3364
  work := work3364
  center_sq := center_sq3364
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3364.1
  jac_ok := checks3364.2.1
  accepted := checks3364.2.2

def tau3365 : RatBall :=
  ⟨⟨-59/640, 241/640⟩, 3/1280⟩
def center3365 : GaussianRat :=
  ⟨-37245497/500000000, 8499173/31250000⟩
def contact3365 : RatBall := localContactBall tau3365 center3365
def work3365 : RoundedTauEval :=
  evalTau precision tau3365 contact3365 logTwoBall

theorem center_sq3365 : (center3365.re : ℝ)^2 +
    (center3365.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3365]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3365 : work3365.theta.ok = true ∧
    work3365.jac.invOK = true ∧ acceptsUnitSq work3365.out = true := by
  norm_num [work3365, contact3365, tau3365, center3365, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3365 : CellCertificate where
  tauBall := tau3365
  contactCenter := center3365
  contactBall := contact3365
  work := work3365
  center_sq := center_sq3365
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3365.1
  jac_ok := checks3365.2.1
  accepted := checks3365.2.2

def tau3366 : RatBall :=
  ⟨⟨-57/640, 241/640⟩, 3/1280⟩
def center3366 : GaussianRat :=
  ⟨-1439861/20000000, 68044601/250000000⟩
def contact3366 : RatBall := localContactBall tau3366 center3366
def work3366 : RoundedTauEval :=
  evalTau precision tau3366 contact3366 logTwoBall

theorem center_sq3366 : (center3366.re : ℝ)^2 +
    (center3366.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3366]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3366 : work3366.theta.ok = true ∧
    work3366.jac.invOK = true ∧ acceptsUnitSq work3366.out = true := by
  norm_num [work3366, contact3366, tau3366, center3366, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3366 : CellCertificate where
  tauBall := tau3366
  contactCenter := center3366
  contactBall := contact3366
  work := work3366
  center_sq := center_sq3366
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3366.1
  jac_ok := checks3366.2.1
  accepted := checks3366.2.2

def tau3367 : RatBall :=
  ⟨⟨-59/640, 243/640⟩, 3/1280⟩
def center3367 : GaussianRat :=
  ⟨-74700643/1000000000, 13723671/50000000⟩
def contact3367 : RatBall := localContactBall tau3367 center3367
def work3367 : RoundedTauEval :=
  evalTau precision tau3367 contact3367 logTwoBall

theorem center_sq3367 : (center3367.re : ℝ)^2 +
    (center3367.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3367]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3367 : work3367.theta.ok = true ∧
    work3367.jac.invOK = true ∧ acceptsUnitSq work3367.out = true := by
  norm_num [work3367, contact3367, tau3367, center3367, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3367 : CellCertificate where
  tauBall := tau3367
  contactCenter := center3367
  contactBall := contact3367
  work := work3367
  center_sq := center_sq3367
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3367.1
  jac_ok := checks3367.2.1
  accepted := checks3367.2.2

def cells : List CellCertificate := [cell3360, cell3361, cell3362, cell3363, cell3364, cell3365, cell3366, cell3367]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420
