import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0414

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3312 : RatBall :=
  ⟨⟨-77/640, 237/640⟩, 3/1280⟩
def center3312 : GaussianRat :=
  ⟨-96307191/1000000000, 264911783/1000000000⟩
def contact3312 : RatBall := localContactBall tau3312 center3312
def work3312 : RoundedTauEval :=
  evalTau precision tau3312 contact3312 logTwoBall

theorem center_sq3312 : (center3312.re : ℝ)^2 +
    (center3312.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3312]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3312 : work3312.theta.ok = true ∧
    work3312.jac.invOK = true ∧ acceptsUnitSq work3312.out = true := by
  norm_num [work3312, contact3312, tau3312, center3312, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3312 : CellCertificate where
  tauBall := tau3312
  contactCenter := center3312
  contactBall := contact3312
  work := work3312
  center_sq := center_sq3312
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3312.1
  jac_ok := checks3312.2.1
  accepted := checks3312.2.2

def tau3313 : RatBall :=
  ⟨⟨-79/640, 239/640⟩, 3/1280⟩
def center3313 : GaussianRat :=
  ⟨-99027743/1000000000, 267103523/1000000000⟩
def contact3313 : RatBall := localContactBall tau3313 center3313
def work3313 : RoundedTauEval :=
  evalTau precision tau3313 contact3313 logTwoBall

theorem center_sq3313 : (center3313.re : ℝ)^2 +
    (center3313.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3313]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3313 : work3313.theta.ok = true ∧
    work3313.jac.invOK = true ∧ acceptsUnitSq work3313.out = true := by
  norm_num [work3313, contact3313, tau3313, center3313, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3313 : CellCertificate where
  tauBall := tau3313
  contactCenter := center3313
  contactBall := contact3313
  work := work3313
  center_sq := center_sq3313
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3313.1
  jac_ok := checks3313.2.1
  accepted := checks3313.2.2

def tau3314 : RatBall :=
  ⟨⟨-77/640, 239/640⟩, 3/1280⟩
def center3314 : GaussianRat :=
  ⟨-96568507/1000000000, 66842431/250000000⟩
def contact3314 : RatBall := localContactBall tau3314 center3314
def work3314 : RoundedTauEval :=
  evalTau precision tau3314 contact3314 logTwoBall

theorem center_sq3314 : (center3314.re : ℝ)^2 +
    (center3314.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3314]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3314 : work3314.theta.ok = true ∧
    work3314.jac.invOK = true ∧ acceptsUnitSq work3314.out = true := by
  norm_num [work3314, contact3314, tau3314, center3314, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3314 : CellCertificate where
  tauBall := tau3314
  contactCenter := center3314
  contactBall := contact3314
  work := work3314
  center_sq := center_sq3314
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3314.1
  jac_ok := checks3314.2.1
  accepted := checks3314.2.2

def tau3315 : RatBall :=
  ⟨⟨-15/128, 237/640⟩, 3/1280⟩
def center3315 : GaussianRat :=
  ⟨-46925291/500000000, 53033649/200000000⟩
def contact3315 : RatBall := localContactBall tau3315 center3315
def work3315 : RoundedTauEval :=
  evalTau precision tau3315 contact3315 logTwoBall

theorem center_sq3315 : (center3315.re : ℝ)^2 +
    (center3315.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3315]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3315 : work3315.theta.ok = true ∧
    work3315.jac.invOK = true ∧ acceptsUnitSq work3315.out = true := by
  norm_num [work3315, contact3315, tau3315, center3315, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3315 : CellCertificate where
  tauBall := tau3315
  contactCenter := center3315
  contactBall := contact3315
  work := work3315
  center_sq := center_sq3315
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3315.1
  jac_ok := checks3315.2.1
  accepted := checks3315.2.2

def tau3316 : RatBall :=
  ⟨⟨-73/640, 237/640⟩, 3/1280⟩
def center3316 : GaussianRat :=
  ⟨-45695259/500000000, 6635463/25000000⟩
def contact3316 : RatBall := localContactBall tau3316 center3316
def work3316 : RoundedTauEval :=
  evalTau precision tau3316 contact3316 logTwoBall

theorem center_sq3316 : (center3316.re : ℝ)^2 +
    (center3316.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3316]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3316 : work3316.theta.ok = true ∧
    work3316.jac.invOK = true ∧ acceptsUnitSq work3316.out = true := by
  norm_num [work3316, contact3316, tau3316, center3316, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3316 : CellCertificate where
  tauBall := tau3316
  contactCenter := center3316
  contactBall := contact3316
  work := work3316
  center_sq := center_sq3316
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3316.1
  jac_ok := checks3316.2.1
  accepted := checks3316.2.2

def tau3317 : RatBall :=
  ⟨⟨-15/128, 239/640⟩, 3/1280⟩
def center3317 : GaussianRat :=
  ⟨-23526423/250000000, 133814851/500000000⟩
def contact3317 : RatBall := localContactBall tau3317 center3317
def work3317 : RoundedTauEval :=
  evalTau precision tau3317 contact3317 logTwoBall

theorem center_sq3317 : (center3317.re : ℝ)^2 +
    (center3317.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3317]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3317 : work3317.theta.ok = true ∧
    work3317.jac.invOK = true ∧ acceptsUnitSq work3317.out = true := by
  norm_num [work3317, contact3317, tau3317, center3317, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3317 : CellCertificate where
  tauBall := tau3317
  contactCenter := center3317
  contactBall := contact3317
  work := work3317
  center_sq := center_sq3317
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3317.1
  jac_ok := checks3317.2.1
  accepted := checks3317.2.2

def tau3318 : RatBall :=
  ⟨⟨-73/640, 239/640⟩, 3/1280⟩
def center3318 : GaussianRat :=
  ⟨-91639379/1000000000, 267883413/1000000000⟩
def contact3318 : RatBall := localContactBall tau3318 center3318
def work3318 : RoundedTauEval :=
  evalTau precision tau3318 contact3318 logTwoBall

theorem center_sq3318 : (center3318.re : ℝ)^2 +
    (center3318.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3318]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3318 : work3318.theta.ok = true ∧
    work3318.jac.invOK = true ∧ acceptsUnitSq work3318.out = true := by
  norm_num [work3318, contact3318, tau3318, center3318, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3318 : CellCertificate where
  tauBall := tau3318
  contactCenter := center3318
  contactBall := contact3318
  work := work3318
  center_sq := center_sq3318
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3318.1
  jac_ok := checks3318.2.1
  accepted := checks3318.2.2

def tau3319 : RatBall :=
  ⟨⟨-71/640, 237/640⟩, 3/1280⟩
def center3319 : GaussianRat :=
  ⟨-2223177/25000000, 53132513/200000000⟩
def contact3319 : RatBall := localContactBall tau3319 center3319
def work3319 : RoundedTauEval :=
  evalTau precision tau3319 contact3319 logTwoBall

theorem center_sq3319 : (center3319.re : ℝ)^2 +
    (center3319.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3319]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3319 : work3319.theta.ok = true ∧
    work3319.jac.invOK = true ∧ acceptsUnitSq work3319.out = true := by
  norm_num [work3319, contact3319, tau3319, center3319, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3319 : CellCertificate where
  tauBall := tau3319
  contactCenter := center3319
  contactBall := contact3319
  work := work3319
  center_sq := center_sq3319
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3319.1
  jac_ok := checks3319.2.1
  accepted := checks3319.2.2

def cells : List CellCertificate := [cell3312, cell3313, cell3314, cell3315, cell3316, cell3317, cell3318, cell3319]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0414
