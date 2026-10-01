import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3824 : RatBall :=
  ⟨⟨113/640, 231/640⟩, 3/1280⟩
def center3824 : GaussianRat :=
  ⟨138783923/1000000000, 252176463/1000000000⟩
def contact3824 : RatBall := localContactBall tau3824 center3824
def work3824 : RoundedTauEval :=
  evalTau precision tau3824 contact3824 logTwoBall

theorem center_sq3824 : (center3824.re : ℝ)^2 +
    (center3824.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3824]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3824 : work3824.theta.ok = true ∧
    work3824.jac.invOK = true ∧ acceptsUnitSq work3824.out = true := by
  norm_num [work3824, contact3824, tau3824, center3824, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3824 : CellCertificate where
  tauBall := tau3824
  contactCenter := center3824
  contactBall := contact3824
  work := work3824
  center_sq := center_sq3824
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3824.1
  jac_ok := checks3824.2.1
  accepted := checks3824.2.2

def tau3825 : RatBall :=
  ⟨⟨117/640, 229/640⟩, 3/1280⟩
def center3825 : GaussianRat :=
  ⟨143146729/1000000000, 249118251/1000000000⟩
def contact3825 : RatBall := localContactBall tau3825 center3825
def work3825 : RoundedTauEval :=
  evalTau precision tau3825 contact3825 logTwoBall

theorem center_sq3825 : (center3825.re : ℝ)^2 +
    (center3825.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3825]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3825 : work3825.theta.ok = true ∧
    work3825.jac.invOK = true ∧ acceptsUnitSq work3825.out = true := by
  norm_num [work3825, contact3825, tau3825, center3825, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3825 : CellCertificate where
  tauBall := tau3825
  contactCenter := center3825
  contactBall := contact3825
  work := work3825
  center_sq := center_sq3825
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3825.1
  jac_ok := checks3825.2.1
  accepted := checks3825.2.2

def tau3826 : RatBall :=
  ⟨⟨121/640, 45/128⟩, 3/1280⟩
def center3826 : GaussianRat :=
  ⟨36780017/250000000, 243731207/1000000000⟩
def contact3826 : RatBall := localContactBall tau3826 center3826
def work3826 : RoundedTauEval :=
  evalTau precision tau3826 contact3826 logTwoBall

theorem center_sq3826 : (center3826.re : ℝ)^2 +
    (center3826.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3826]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3826 : work3826.theta.ok = true ∧
    work3826.jac.invOK = true ∧ acceptsUnitSq work3826.out = true := by
  norm_num [work3826, contact3826, tau3826, center3826, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3826 : CellCertificate where
  tauBall := tau3826
  contactCenter := center3826
  contactBall := contact3826
  work := work3826
  center_sq := center_sq3826
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3826.1
  jac_ok := checks3826.2.1
  accepted := checks3826.2.2

def tau3827 : RatBall :=
  ⟨⟨123/640, 45/128⟩, 3/1280⟩
def center3827 : GaussianRat :=
  ⟨149448351/1000000000, 9735017/40000000⟩
def contact3827 : RatBall := localContactBall tau3827 center3827
def work3827 : RoundedTauEval :=
  evalTau precision tau3827 contact3827 logTwoBall

theorem center_sq3827 : (center3827.re : ℝ)^2 +
    (center3827.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3827]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3827 : work3827.theta.ok = true ∧
    work3827.jac.invOK = true ∧ acceptsUnitSq work3827.out = true := by
  norm_num [work3827, contact3827, tau3827, center3827, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3827 : CellCertificate where
  tauBall := tau3827
  contactCenter := center3827
  contactBall := contact3827
  work := work3827
  center_sq := center_sq3827
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3827.1
  jac_ok := checks3827.2.1
  accepted := checks3827.2.2

def tau3828 : RatBall :=
  ⟨⟨121/640, 227/640⟩, 3/1280⟩
def center3828 : GaussianRat :=
  ⟨147475889/1000000000, 123032099/500000000⟩
def contact3828 : RatBall := localContactBall tau3828 center3828
def work3828 : RoundedTauEval :=
  evalTau precision tau3828 contact3828 logTwoBall

theorem center_sq3828 : (center3828.re : ℝ)^2 +
    (center3828.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3828]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3828 : work3828.theta.ok = true ∧
    work3828.jac.invOK = true ∧ acceptsUnitSq work3828.out = true := by
  norm_num [work3828, contact3828, tau3828, center3828, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3828 : CellCertificate where
  tauBall := tau3828
  contactCenter := center3828
  contactBall := contact3828
  work := work3828
  center_sq := center_sq3828
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3828.1
  jac_ok := checks3828.2.1
  accepted := checks3828.2.2

def tau3829 : RatBall :=
  ⟨⟨141/640, 213/640⟩, 3/1280⟩
def center3829 : GaussianRat :=
  ⟨33577827/200000000, 28294879/125000000⟩
def contact3829 : RatBall := localContactBall tau3829 center3829
def work3829 : RoundedTauEval :=
  evalTau precision tau3829 contact3829 logTwoBall

theorem center_sq3829 : (center3829.re : ℝ)^2 +
    (center3829.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3829]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3829 : work3829.theta.ok = true ∧
    work3829.jac.invOK = true ∧ acceptsUnitSq work3829.out = true := by
  norm_num [work3829, contact3829, tau3829, center3829, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3829 : CellCertificate where
  tauBall := tau3829
  contactCenter := center3829
  contactBall := contact3829
  work := work3829
  center_sq := center_sq3829
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3829.1
  jac_ok := checks3829.2.1
  accepted := checks3829.2.2

def tau3830 : RatBall :=
  ⟨⟨143/640, 213/640⟩, 3/1280⟩
def center3830 : GaussianRat :=
  ⟨85071813/500000000, 28248739/125000000⟩
def contact3830 : RatBall := localContactBall tau3830 center3830
def work3830 : RoundedTauEval :=
  evalTau precision tau3830 contact3830 logTwoBall

theorem center_sq3830 : (center3830.re : ℝ)^2 +
    (center3830.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3830]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3830 : work3830.theta.ok = true ∧
    work3830.jac.invOK = true ∧ acceptsUnitSq work3830.out = true := by
  norm_num [work3830, contact3830, tau3830, center3830, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3830 : CellCertificate where
  tauBall := tau3830
  contactCenter := center3830
  contactBall := contact3830
  work := work3830
  center_sq := center_sq3830
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3830.1
  jac_ok := checks3830.2.1
  accepted := checks3830.2.2

def tau3831 : RatBall :=
  ⟨⟨141/640, 43/128⟩, 3/1280⟩
def center3831 : GaussianRat :=
  ⟨84129393/500000000, 228617923/1000000000⟩
def contact3831 : RatBall := localContactBall tau3831 center3831
def work3831 : RoundedTauEval :=
  evalTau precision tau3831 contact3831 logTwoBall

theorem center_sq3831 : (center3831.re : ℝ)^2 +
    (center3831.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3831]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3831 : work3831.theta.ok = true ∧
    work3831.jac.invOK = true ∧ acceptsUnitSq work3831.out = true := by
  norm_num [work3831, contact3831, tau3831, center3831, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3831 : CellCertificate where
  tauBall := tau3831
  contactCenter := center3831
  contactBall := contact3831
  work := work3831
  center_sq := center_sq3831
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3831.1
  jac_ok := checks3831.2.1
  accepted := checks3831.2.2

def cells : List CellCertificate := [cell3824, cell3825, cell3826, cell3827, cell3828, cell3829, cell3830, cell3831]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478
