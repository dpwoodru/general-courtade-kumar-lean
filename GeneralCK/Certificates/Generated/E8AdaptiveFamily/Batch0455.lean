import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3640 : RatBall :=
  ⟨⟨41/640, 253/640⟩, 3/1280⟩
def center3640 : GaussianRat :=
  ⟨52835321/1000000000, 11552523/40000000⟩
def contact3640 : RatBall := localContactBall tau3640 center3640
def work3640 : RoundedTauEval :=
  evalTau precision tau3640 contact3640 logTwoBall

theorem center_sq3640 : (center3640.re : ℝ)^2 +
    (center3640.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3640]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3640 : work3640.theta.ok = true ∧
    work3640.jac.invOK = true ∧ acceptsUnitSq work3640.out = true := by
  norm_num [work3640, contact3640, tau3640, center3640, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3640 : CellCertificate where
  tauBall := tau3640
  contactCenter := center3640
  contactBall := contact3640
  work := work3640
  center_sq := center_sq3640
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3640.1
  jac_ok := checks3640.2.1
  accepted := checks3640.2.2

def tau3641 : RatBall :=
  ⟨⟨43/640, 253/640⟩, 3/1280⟩
def center3641 : GaussianRat :=
  ⟨55396349/1000000000, 28864989/100000000⟩
def contact3641 : RatBall := localContactBall tau3641 center3641
def work3641 : RoundedTauEval :=
  evalTau precision tau3641 contact3641 logTwoBall

theorem center_sq3641 : (center3641.re : ℝ)^2 +
    (center3641.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3641]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3641 : work3641.theta.ok = true ∧
    work3641.jac.invOK = true ∧ acceptsUnitSq work3641.out = true := by
  norm_num [work3641, contact3641, tau3641, center3641, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3641 : CellCertificate where
  tauBall := tau3641
  contactCenter := center3641
  contactBall := contact3641
  work := work3641
  center_sq := center_sq3641
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3641.1
  jac_ok := checks3641.2.1
  accepted := checks3641.2.2

def tau3642 : RatBall :=
  ⟨⟨9/128, 253/640⟩, 3/1280⟩
def center3642 : GaussianRat :=
  ⟨5795507/100000000, 288479173/1000000000⟩
def contact3642 : RatBall := localContactBall tau3642 center3642
def work3642 : RoundedTauEval :=
  evalTau precision tau3642 contact3642 logTwoBall

theorem center_sq3642 : (center3642.re : ℝ)^2 +
    (center3642.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3642]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3642 : work3642.theta.ok = true ∧
    work3642.jac.invOK = true ∧ acceptsUnitSq work3642.out = true := by
  norm_num [work3642, contact3642, tau3642, center3642, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3642 : CellCertificate where
  tauBall := tau3642
  contactCenter := center3642
  contactBall := contact3642
  work := work3642
  center_sq := center_sq3642
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3642.1
  jac_ok := checks3642.2.1
  accepted := checks3642.2.2

def tau3643 : RatBall :=
  ⟨⟨49/640, 241/640⟩, 3/1280⟩
def center3643 : GaussianRat :=
  ⟨12394897/200000000, 272930361/1000000000⟩
def contact3643 : RatBall := localContactBall tau3643 center3643
def work3643 : RoundedTauEval :=
  evalTau precision tau3643 contact3643 logTwoBall

theorem center_sq3643 : (center3643.re : ℝ)^2 +
    (center3643.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3643]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3643 : work3643.theta.ok = true ∧
    work3643.jac.invOK = true ∧ acceptsUnitSq work3643.out = true := by
  norm_num [work3643, contact3643, tau3643, center3643, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3643 : CellCertificate where
  tauBall := tau3643
  contactCenter := center3643
  contactBall := contact3643
  work := work3643
  center_sq := center_sq3643
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3643.1
  jac_ok := checks3643.2.1
  accepted := checks3643.2.2

def tau3644 : RatBall :=
  ⟨⟨51/640, 241/640⟩, 3/1280⟩
def center3644 : GaussianRat :=
  ⟨16120741/250000000, 34094071/125000000⟩
def contact3644 : RatBall := localContactBall tau3644 center3644
def work3644 : RoundedTauEval :=
  evalTau precision tau3644 contact3644 logTwoBall

theorem center_sq3644 : (center3644.re : ℝ)^2 +
    (center3644.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3644]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3644 : work3644.theta.ok = true ∧
    work3644.jac.invOK = true ∧ acceptsUnitSq work3644.out = true := by
  norm_num [work3644, contact3644, tau3644, center3644, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3644 : CellCertificate where
  tauBall := tau3644
  contactCenter := center3644
  contactBall := contact3644
  work := work3644
  center_sq := center_sq3644
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3644.1
  jac_ok := checks3644.2.1
  accepted := checks3644.2.2

def tau3645 : RatBall :=
  ⟨⟨49/640, 243/640⟩, 3/1280⟩
def center3645 : GaussianRat :=
  ⟨12430013/200000000, 275443499/1000000000⟩
def contact3645 : RatBall := localContactBall tau3645 center3645
def work3645 : RoundedTauEval :=
  evalTau precision tau3645 contact3645 logTwoBall

theorem center_sq3645 : (center3645.re : ℝ)^2 +
    (center3645.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3645]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3645 : work3645.theta.ok = true ∧
    work3645.jac.invOK = true ∧ acceptsUnitSq work3645.out = true := by
  norm_num [work3645, contact3645, tau3645, center3645, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3645 : CellCertificate where
  tauBall := tau3645
  contactCenter := center3645
  contactBall := contact3645
  work := work3645
  center_sq := center_sq3645
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3645.1
  jac_ok := checks3645.2.1
  accepted := checks3645.2.2

def tau3646 : RatBall :=
  ⟨⟨51/640, 243/640⟩, 3/1280⟩
def center3646 : GaussianRat :=
  ⟨32332713/500000000, 275263239/1000000000⟩
def contact3646 : RatBall := localContactBall tau3646 center3646
def work3646 : RoundedTauEval :=
  evalTau precision tau3646 contact3646 logTwoBall

theorem center_sq3646 : (center3646.re : ℝ)^2 +
    (center3646.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3646]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3646 : work3646.theta.ok = true ∧
    work3646.jac.invOK = true ∧ acceptsUnitSq work3646.out = true := by
  norm_num [work3646, contact3646, tau3646, center3646, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3646 : CellCertificate where
  tauBall := tau3646
  contactCenter := center3646
  contactBall := contact3646
  work := work3646
  center_sq := center_sq3646
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3646.1
  jac_ok := checks3646.2.1
  accepted := checks3646.2.2

def tau3647 : RatBall :=
  ⟨⟨53/640, 241/640⟩, 3/1280⟩
def center3647 : GaussianRat :=
  ⟨13397789/200000000, 54513591/200000000⟩
def contact3647 : RatBall := localContactBall tau3647 center3647
def work3647 : RoundedTauEval :=
  evalTau precision tau3647 contact3647 logTwoBall

theorem center_sq3647 : (center3647.re : ℝ)^2 +
    (center3647.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3647]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3647 : work3647.theta.ok = true ∧
    work3647.jac.invOK = true ∧ acceptsUnitSq work3647.out = true := by
  norm_num [work3647, contact3647, tau3647, center3647, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3647 : CellCertificate where
  tauBall := tau3647
  contactCenter := center3647
  contactBall := contact3647
  work := work3647
  center_sq := center_sq3647
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3647.1
  jac_ok := checks3647.2.1
  accepted := checks3647.2.2

def cells : List CellCertificate := [cell3640, cell3641, cell3642, cell3643, cell3644, cell3645, cell3646, cell3647]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455
