import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0479

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3832 : RatBall :=
  ⟨⟨129/640, 217/640⟩, 3/1280⟩
def center3832 : GaussianRat :=
  ⟨38739093/250000000, 233070213/1000000000⟩
def contact3832 : RatBall := localContactBall tau3832 center3832
def work3832 : RoundedTauEval :=
  evalTau precision tau3832 contact3832 logTwoBall

theorem center_sq3832 : (center3832.re : ℝ)^2 +
    (center3832.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3832]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3832 : work3832.theta.ok = true ∧
    work3832.jac.invOK = true ∧ acceptsUnitSq work3832.out = true := by
  norm_num [work3832, contact3832, tau3832, center3832, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3832 : CellCertificate where
  tauBall := tau3832
  contactCenter := center3832
  contactBall := contact3832
  work := work3832
  center_sq := center_sq3832
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3832.1
  jac_ok := checks3832.2.1
  accepted := checks3832.2.2

def tau3833 : RatBall :=
  ⟨⟨131/640, 217/640⟩, 3/1280⟩
def center3833 : GaussianRat :=
  ⟨157247951/1000000000, 46543131/200000000⟩
def contact3833 : RatBall := localContactBall tau3833 center3833
def work3833 : RoundedTauEval :=
  evalTau precision tau3833 contact3833 logTwoBall

theorem center_sq3833 : (center3833.re : ℝ)^2 +
    (center3833.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3833]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3833 : work3833.theta.ok = true ∧
    work3833.jac.invOK = true ∧ acceptsUnitSq work3833.out = true := by
  norm_num [work3833, contact3833, tau3833, center3833, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3833 : CellCertificate where
  tauBall := tau3833
  contactCenter := center3833
  contactBall := contact3833
  work := work3833
  center_sq := center_sq3833
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3833.1
  jac_ok := checks3833.2.1
  accepted := checks3833.2.2

def tau3834 : RatBall :=
  ⟨⟨129/640, 219/640⟩, 3/1280⟩
def center3834 : GaussianRat :=
  ⟨155311177/1000000000, 29420787/125000000⟩
def contact3834 : RatBall := localContactBall tau3834 center3834
def work3834 : RoundedTauEval :=
  evalTau precision tau3834 contact3834 logTwoBall

theorem center_sq3834 : (center3834.re : ℝ)^2 +
    (center3834.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3834]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3834 : work3834.theta.ok = true ∧
    work3834.jac.invOK = true ∧ acceptsUnitSq work3834.out = true := by
  norm_num [work3834, contact3834, tau3834, center3834, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3834 : CellCertificate where
  tauBall := tau3834
  contactCenter := center3834
  contactBall := contact3834
  work := work3834
  center_sq := center_sq3834
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3834.1
  jac_ok := checks3834.2.1
  accepted := checks3834.2.2

def tau3835 : RatBall :=
  ⟨⟨131/640, 219/640⟩, 3/1280⟩
def center3835 : GaussianRat :=
  ⟨157607013/1000000000, 23500697/100000000⟩
def contact3835 : RatBall := localContactBall tau3835 center3835
def work3835 : RoundedTauEval :=
  evalTau precision tau3835 contact3835 logTwoBall

theorem center_sq3835 : (center3835.re : ℝ)^2 +
    (center3835.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3835]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3835 : work3835.theta.ok = true ∧
    work3835.jac.invOK = true ∧ acceptsUnitSq work3835.out = true := by
  norm_num [work3835, contact3835, tau3835, center3835, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3835 : CellCertificate where
  tauBall := tau3835
  contactCenter := center3835
  contactBall := contact3835
  work := work3835
  center_sq := center_sq3835
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3835.1
  jac_ok := checks3835.2.1
  accepted := checks3835.2.2

def tau3836 : RatBall :=
  ⟨⟨133/640, 217/640⟩, 3/1280⟩
def center3836 : GaussianRat :=
  ⟨79767381/500000000, 29044611/125000000⟩
def contact3836 : RatBall := localContactBall tau3836 center3836
def work3836 : RoundedTauEval :=
  evalTau precision tau3836 contact3836 logTwoBall

theorem center_sq3836 : (center3836.re : ℝ)^2 +
    (center3836.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3836]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3836 : work3836.theta.ok = true ∧
    work3836.jac.invOK = true ∧ acceptsUnitSq work3836.out = true := by
  norm_num [work3836, contact3836, tau3836, center3836, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3836 : CellCertificate where
  tauBall := tau3836
  contactCenter := center3836
  contactBall := contact3836
  work := work3836
  center_sq := center_sq3836
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3836.1
  jac_ok := checks3836.2.1
  accepted := checks3836.2.2

def tau3837 : RatBall :=
  ⟨⟨27/128, 217/640⟩, 3/1280⟩
def center3837 : GaussianRat :=
  ⟨80908379/500000000, 115996981/500000000⟩
def contact3837 : RatBall := localContactBall tau3837 center3837
def work3837 : RoundedTauEval :=
  evalTau precision tau3837 contact3837 logTwoBall

theorem center_sq3837 : (center3837.re : ℝ)^2 +
    (center3837.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3837]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3837 : work3837.theta.ok = true ∧
    work3837.jac.invOK = true ∧ acceptsUnitSq work3837.out = true := by
  norm_num [work3837, contact3837, tau3837, center3837, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3837 : CellCertificate where
  tauBall := tau3837
  contactCenter := center3837
  contactBall := contact3837
  work := work3837
  center_sq := center_sq3837
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3837.1
  jac_ok := checks3837.2.1
  accepted := checks3837.2.2

def tau3838 : RatBall :=
  ⟨⟨133/640, 219/640⟩, 3/1280⟩
def center3838 : GaussianRat :=
  ⟨159898033/1000000000, 234643387/1000000000⟩
def contact3838 : RatBall := localContactBall tau3838 center3838
def work3838 : RoundedTauEval :=
  evalTau precision tau3838 contact3838 logTwoBall

theorem center_sq3838 : (center3838.re : ℝ)^2 +
    (center3838.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3838]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3838 : work3838.theta.ok = true ∧
    work3838.jac.invOK = true ∧ acceptsUnitSq work3838.out = true := by
  norm_num [work3838, contact3838, tau3838, center3838, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3838 : CellCertificate where
  tauBall := tau3838
  contactCenter := center3838
  contactBall := contact3838
  work := work3838
  center_sq := center_sq3838
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3838.1
  jac_ok := checks3838.2.1
  accepted := checks3838.2.2

def tau3839 : RatBall :=
  ⟨⟨27/128, 219/640⟩, 3/1280⟩
def center3839 : GaussianRat :=
  ⟨162184187/1000000000, 234275597/1000000000⟩
def contact3839 : RatBall := localContactBall tau3839 center3839
def work3839 : RoundedTauEval :=
  evalTau precision tau3839 contact3839 logTwoBall

theorem center_sq3839 : (center3839.re : ℝ)^2 +
    (center3839.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3839]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3839 : work3839.theta.ok = true ∧
    work3839.jac.invOK = true ∧ acceptsUnitSq work3839.out = true := by
  norm_num [work3839, contact3839, tau3839, center3839, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3839 : CellCertificate where
  tauBall := tau3839
  contactCenter := center3839
  contactBall := contact3839
  work := work3839
  center_sq := center_sq3839
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3839.1
  jac_ok := checks3839.2.1
  accepted := checks3839.2.2

def cells : List CellCertificate := [cell3832, cell3833, cell3834, cell3835, cell3836, cell3837, cell3838, cell3839]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0479
