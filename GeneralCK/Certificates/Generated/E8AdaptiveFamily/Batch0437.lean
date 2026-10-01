import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0437

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3496 : RatBall :=
  ⟨⟨-11/640, 249/640⟩, 3/1280⟩
def center3496 : GaussianRat :=
  ⟨-14128883/1000000000, 11407523/40000000⟩
def contact3496 : RatBall := localContactBall tau3496 center3496
def work3496 : RoundedTauEval :=
  evalTau precision tau3496 contact3496 logTwoBall

theorem center_sq3496 : (center3496.re : ℝ)^2 +
    (center3496.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3496]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3496 : work3496.theta.ok = true ∧
    work3496.jac.invOK = true ∧ acceptsUnitSq work3496.out = true := by
  norm_num [work3496, contact3496, tau3496, center3496, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3496 : CellCertificate where
  tauBall := tau3496
  contactCenter := center3496
  contactBall := contact3496
  work := work3496
  center_sq := center_sq3496
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3496.1
  jac_ok := checks3496.2.1
  accepted := checks3496.2.2

def tau3497 : RatBall :=
  ⟨⟨-9/640, 249/640⟩, 3/1280⟩
def center3497 : GaussianRat :=
  ⟨-2890199/250000000, 14261319/50000000⟩
def contact3497 : RatBall := localContactBall tau3497 center3497
def work3497 : RoundedTauEval :=
  evalTau precision tau3497 contact3497 logTwoBall

theorem center_sq3497 : (center3497.re : ℝ)^2 +
    (center3497.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3497]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3497 : work3497.theta.ok = true ∧
    work3497.jac.invOK = true ∧ acceptsUnitSq work3497.out = true := by
  norm_num [work3497, contact3497, tau3497, center3497, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3497 : CellCertificate where
  tauBall := tau3497
  contactCenter := center3497
  contactBall := contact3497
  work := work3497
  center_sq := center_sq3497
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3497.1
  jac_ok := checks3497.2.1
  accepted := checks3497.2.2

def tau3498 : RatBall :=
  ⟨⟨-11/640, 251/640⟩, 3/1280⟩
def center3498 : GaussianRat :=
  ⟨-14171307/1000000000, 287759727/1000000000⟩
def contact3498 : RatBall := localContactBall tau3498 center3498
def work3498 : RoundedTauEval :=
  evalTau precision tau3498 contact3498 logTwoBall

theorem center_sq3498 : (center3498.re : ℝ)^2 +
    (center3498.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3498]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3498 : work3498.theta.ok = true ∧
    work3498.jac.invOK = true ∧ acceptsUnitSq work3498.out = true := by
  norm_num [work3498, contact3498, tau3498, center3498, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3498 : CellCertificate where
  tauBall := tau3498
  contactCenter := center3498
  contactBall := contact3498
  work := work3498
  center_sq := center_sq3498
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3498.1
  jac_ok := checks3498.2.1
  accepted := checks3498.2.2

def tau3499 : RatBall :=
  ⟨⟨-9/640, 251/640⟩, 3/1280⟩
def center3499 : GaussianRat :=
  ⟨-5797759/500000000, 28779857/100000000⟩
def contact3499 : RatBall := localContactBall tau3499 center3499
def work3499 : RoundedTauEval :=
  evalTau precision tau3499 contact3499 logTwoBall

theorem center_sq3499 : (center3499.re : ℝ)^2 +
    (center3499.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3499]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3499 : work3499.theta.ok = true ∧
    work3499.jac.invOK = true ∧ acceptsUnitSq work3499.out = true := by
  norm_num [work3499, contact3499, tau3499, center3499, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3499 : CellCertificate where
  tauBall := tau3499
  contactCenter := center3499
  contactBall := contact3499
  work := work3499
  center_sq := center_sq3499
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3499.1
  jac_ok := checks3499.2.1
  accepted := checks3499.2.2

def tau3500 : RatBall :=
  ⟨⟨-3/128, 253/640⟩, 3/1280⟩
def center3500 : GaussianRat :=
  ⟨-19379607/1000000000, 58047357/200000000⟩
def contact3500 : RatBall := localContactBall tau3500 center3500
def work3500 : RoundedTauEval :=
  evalTau precision tau3500 contact3500 logTwoBall

theorem center_sq3500 : (center3500.re : ℝ)^2 +
    (center3500.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3500]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3500 : work3500.theta.ok = true ∧
    work3500.jac.invOK = true ∧ acceptsUnitSq work3500.out = true := by
  norm_num [work3500, contact3500, tau3500, center3500, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3500 : CellCertificate where
  tauBall := tau3500
  contactCenter := center3500
  contactBall := contact3500
  work := work3500
  center_sq := center_sq3500
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3500.1
  jac_ok := checks3500.2.1
  accepted := checks3500.2.2

def tau3501 : RatBall :=
  ⟨⟨-13/640, 253/640⟩, 3/1280⟩
def center3501 : GaussianRat :=
  ⟨-16797323/1000000000, 290291883/1000000000⟩
def contact3501 : RatBall := localContactBall tau3501 center3501
def work3501 : RoundedTauEval :=
  evalTau precision tau3501 contact3501 logTwoBall

theorem center_sq3501 : (center3501.re : ℝ)^2 +
    (center3501.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3501]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3501 : work3501.theta.ok = true ∧
    work3501.jac.invOK = true ∧ acceptsUnitSq work3501.out = true := by
  norm_num [work3501, contact3501, tau3501, center3501, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3501 : CellCertificate where
  tauBall := tau3501
  contactCenter := center3501
  contactBall := contact3501
  work := work3501
  center_sq := center_sq3501
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3501.1
  jac_ok := checks3501.2.1
  accepted := checks3501.2.2

def tau3502 : RatBall :=
  ⟨⟨-3/128, 51/128⟩, 3/1280⟩
def center3502 : GaussianRat :=
  ⟨-60747/3125000, 58564523/200000000⟩
def contact3502 : RatBall := localContactBall tau3502 center3502
def work3502 : RoundedTauEval :=
  evalTau precision tau3502 contact3502 logTwoBall

theorem center_sq3502 : (center3502.re : ℝ)^2 +
    (center3502.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3502]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3502 : work3502.theta.ok = true ∧
    work3502.jac.invOK = true ∧ acceptsUnitSq work3502.out = true := by
  norm_num [work3502, contact3502, tau3502, center3502, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3502 : CellCertificate where
  tauBall := tau3502
  contactCenter := center3502
  contactBall := contact3502
  work := work3502
  center_sq := center_sq3502
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3502.1
  jac_ok := checks3502.2.1
  accepted := checks3502.2.2

def tau3503 : RatBall :=
  ⟨⟨-13/640, 51/128⟩, 3/1280⟩
def center3503 : GaussianRat :=
  ⟨-3369771/200000000, 146439243/500000000⟩
def contact3503 : RatBall := localContactBall tau3503 center3503
def work3503 : RoundedTauEval :=
  evalTau precision tau3503 contact3503 logTwoBall

theorem center_sq3503 : (center3503.re : ℝ)^2 +
    (center3503.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3503]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3503 : work3503.theta.ok = true ∧
    work3503.jac.invOK = true ∧ acceptsUnitSq work3503.out = true := by
  norm_num [work3503, contact3503, tau3503, center3503, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3503 : CellCertificate where
  tauBall := tau3503
  contactCenter := center3503
  contactBall := contact3503
  work := work3503
  center_sq := center_sq3503
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3503.1
  jac_ok := checks3503.2.1
  accepted := checks3503.2.2

def cells : List CellCertificate := [cell3496, cell3497, cell3498, cell3499, cell3500, cell3501, cell3502, cell3503]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0437
