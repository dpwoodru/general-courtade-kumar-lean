import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3544 : RatBall :=
  ⟨⟨13/640, 249/640⟩, 3/1280⟩
def center3544 : GaussianRat :=
  ⟨3339277/200000000, 71285531/250000000⟩
def contact3544 : RatBall := localContactBall tau3544 center3544
def work3544 : RoundedTauEval :=
  evalTau precision tau3544 contact3544 logTwoBall

theorem center_sq3544 : (center3544.re : ℝ)^2 +
    (center3544.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3544]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3544 : work3544.theta.ok = true ∧
    work3544.jac.invOK = true ∧ acceptsUnitSq work3544.out = true := by
  norm_num [work3544, contact3544, tau3544, center3544, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3544 : CellCertificate where
  tauBall := tau3544
  contactCenter := center3544
  contactBall := contact3544
  work := work3544
  center_sq := center_sq3544
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3544.1
  jac_ok := checks3544.2.1
  accepted := checks3544.2.2

def tau3545 : RatBall :=
  ⟨⟨3/128, 249/640⟩, 3/1280⟩
def center3545 : GaussianRat :=
  ⟨19263193/1000000000, 142544269/500000000⟩
def contact3545 : RatBall := localContactBall tau3545 center3545
def work3545 : RoundedTauEval :=
  evalTau precision tau3545 contact3545 logTwoBall

theorem center_sq3545 : (center3545.re : ℝ)^2 +
    (center3545.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3545]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3545 : work3545.theta.ok = true ∧
    work3545.jac.invOK = true ∧ acceptsUnitSq work3545.out = true := by
  norm_num [work3545, contact3545, tau3545, center3545, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3545 : CellCertificate where
  tauBall := tau3545
  contactCenter := center3545
  contactBall := contact3545
  work := work3545
  center_sq := center_sq3545
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3545.1
  jac_ok := checks3545.2.1
  accepted := checks3545.2.2

def tau3546 : RatBall :=
  ⟨⟨13/640, 251/640⟩, 3/1280⟩
def center3546 : GaussianRat :=
  ⟨8373251/500000000, 287713133/1000000000⟩
def contact3546 : RatBall := localContactBall tau3546 center3546
def work3546 : RoundedTauEval :=
  evalTau precision tau3546 contact3546 logTwoBall

theorem center_sq3546 : (center3546.re : ℝ)^2 +
    (center3546.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3546]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3546 : work3546.theta.ok = true ∧
    work3546.jac.invOK = true ∧ acceptsUnitSq work3546.out = true := by
  norm_num [work3546, contact3546, tau3546, center3546, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3546 : CellCertificate where
  tauBall := tau3546
  contactCenter := center3546
  contactBall := contact3546
  work := work3546
  center_sq := center_sq3546
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3546.1
  jac_ok := checks3546.2.1
  accepted := checks3546.2.2

def tau3547 : RatBall :=
  ⟨⟨3/128, 251/640⟩, 3/1280⟩
def center3547 : GaussianRat :=
  ⟨3864199/200000000, 57531759/200000000⟩
def contact3547 : RatBall := localContactBall tau3547 center3547
def work3547 : RoundedTauEval :=
  evalTau precision tau3547 contact3547 logTwoBall

theorem center_sq3547 : (center3547.re : ℝ)^2 +
    (center3547.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3547]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3547 : work3547.theta.ok = true ∧
    work3547.jac.invOK = true ∧ acceptsUnitSq work3547.out = true := by
  norm_num [work3547, contact3547, tau3547, center3547, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3547 : CellCertificate where
  tauBall := tau3547
  contactCenter := center3547
  contactBall := contact3547
  work := work3547
  center_sq := center_sq3547
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3547.1
  jac_ok := checks3547.2.1
  accepted := checks3547.2.2

def tau3548 : RatBall :=
  ⟨⟨9/640, 253/640⟩, 3/1280⟩
def center3548 : GaussianRat :=
  ⟨5815363/500000000, 145189259/500000000⟩
def contact3548 : RatBall := localContactBall tau3548 center3548
def work3548 : RoundedTauEval :=
  evalTau precision tau3548 contact3548 logTwoBall

theorem center_sq3548 : (center3548.re : ℝ)^2 +
    (center3548.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3548]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3548 : work3548.theta.ok = true ∧
    work3548.jac.invOK = true ∧ acceptsUnitSq work3548.out = true := by
  norm_num [work3548, contact3548, tau3548, center3548, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3548 : CellCertificate where
  tauBall := tau3548
  contactCenter := center3548
  contactBall := contact3548
  work := work3548
  center_sq := center_sq3548
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3548.1
  jac_ok := checks3548.2.1
  accepted := checks3548.2.2

def tau3549 : RatBall :=
  ⟨⟨11/640, 253/640⟩, 3/1280⟩
def center3549 : GaussianRat :=
  ⟨7107163/500000000, 290339131/1000000000⟩
def contact3549 : RatBall := localContactBall tau3549 center3549
def work3549 : RoundedTauEval :=
  evalTau precision tau3549 contact3549 logTwoBall

theorem center_sq3549 : (center3549.re : ℝ)^2 +
    (center3549.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3549]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3549 : work3549.theta.ok = true ∧
    work3549.jac.invOK = true ∧ acceptsUnitSq work3549.out = true := by
  norm_num [work3549, contact3549, tau3549, center3549, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3549 : CellCertificate where
  tauBall := tau3549
  contactCenter := center3549
  contactBall := contact3549
  work := work3549
  center_sq := center_sq3549
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3549.1
  jac_ok := checks3549.2.1
  accepted := checks3549.2.2

def tau3550 : RatBall :=
  ⟨⟨9/640, 51/128⟩, 3/1280⟩
def center3550 : GaussianRat :=
  ⟨11666429/1000000000, 4577599/15625000⟩
def contact3550 : RatBall := localContactBall tau3550 center3550
def work3550 : RoundedTauEval :=
  evalTau precision tau3550 contact3550 logTwoBall

theorem center_sq3550 : (center3550.re : ℝ)^2 +
    (center3550.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3550]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3550 : work3550.theta.ok = true ∧
    work3550.jac.invOK = true ∧ acceptsUnitSq work3550.out = true := by
  norm_num [work3550, contact3550, tau3550, center3550, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3550 : CellCertificate where
  tauBall := tau3550
  contactCenter := center3550
  contactBall := contact3550
  work := work3550
  center_sq := center_sq3550
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3550.1
  jac_ok := checks3550.2.1
  accepted := checks3550.2.2

def tau3551 : RatBall :=
  ⟨⟨11/640, 51/128⟩, 3/1280⟩
def center3551 : GaussianRat :=
  ⟨3564487/250000000, 73231599/250000000⟩
def contact3551 : RatBall := localContactBall tau3551 center3551
def work3551 : RoundedTauEval :=
  evalTau precision tau3551 contact3551 logTwoBall

theorem center_sq3551 : (center3551.re : ℝ)^2 +
    (center3551.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3551]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3551 : work3551.theta.ok = true ∧
    work3551.jac.invOK = true ∧ acceptsUnitSq work3551.out = true := by
  norm_num [work3551, contact3551, tau3551, center3551, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3551 : CellCertificate where
  tauBall := tau3551
  contactCenter := center3551
  contactBall := contact3551
  work := work3551
  center_sq := center_sq3551
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3551.1
  jac_ok := checks3551.2.1
  accepted := checks3551.2.2

def cells : List CellCertificate := [cell3544, cell3545, cell3546, cell3547, cell3548, cell3549, cell3550, cell3551]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443
