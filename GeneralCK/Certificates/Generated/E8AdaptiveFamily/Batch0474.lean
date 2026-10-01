import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3792 : RatBall :=
  ⟨⟨111/640, 227/640⟩, 3/1280⟩
def center3792 : GaussianRat :=
  ⟨135740809/1000000000, 4955901/20000000⟩
def contact3792 : RatBall := localContactBall tau3792 center3792
def work3792 : RoundedTauEval :=
  evalTau precision tau3792 contact3792 logTwoBall

theorem center_sq3792 : (center3792.re : ℝ)^2 +
    (center3792.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3792]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3792 : work3792.theta.ok = true ∧
    work3792.jac.invOK = true ∧ acceptsUnitSq work3792.out = true := by
  norm_num [work3792, contact3792, tau3792, center3792, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3792 : CellCertificate where
  tauBall := tau3792
  contactCenter := center3792
  contactBall := contact3792
  work := work3792
  center_sq := center_sq3792
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3792.1
  jac_ok := checks3792.2.1
  accepted := checks3792.2.2

def tau3793 : RatBall :=
  ⟨⟨21/128, 229/640⟩, 3/1280⟩
def center3793 : GaussianRat :=
  ⟨128966511/1000000000, 50229677/200000000⟩
def contact3793 : RatBall := localContactBall tau3793 center3793
def work3793 : RoundedTauEval :=
  evalTau precision tau3793 contact3793 logTwoBall

theorem center_sq3793 : (center3793.re : ℝ)^2 +
    (center3793.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3793]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3793 : work3793.theta.ok = true ∧
    work3793.jac.invOK = true ∧ acceptsUnitSq work3793.out = true := by
  norm_num [work3793, contact3793, tau3793, center3793, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3793 : CellCertificate where
  tauBall := tau3793
  contactCenter := center3793
  contactBall := contact3793
  work := work3793
  center_sq := center_sq3793
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3793.1
  jac_ok := checks3793.2.1
  accepted := checks3793.2.2

def tau3794 : RatBall :=
  ⟨⟨107/640, 229/640⟩, 3/1280⟩
def center3794 : GaussianRat :=
  ⟨65670547/500000000, 62705679/250000000⟩
def contact3794 : RatBall := localContactBall tau3794 center3794
def work3794 : RoundedTauEval :=
  evalTau precision tau3794 contact3794 logTwoBall

theorem center_sq3794 : (center3794.re : ℝ)^2 +
    (center3794.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3794]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3794 : work3794.theta.ok = true ∧
    work3794.jac.invOK = true ∧ acceptsUnitSq work3794.out = true := by
  norm_num [work3794, contact3794, tau3794, center3794, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3794 : CellCertificate where
  tauBall := tau3794
  contactCenter := center3794
  contactBall := contact3794
  work := work3794
  center_sq := center_sq3794
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3794.1
  jac_ok := checks3794.2.1
  accepted := checks3794.2.2

def tau3795 : RatBall :=
  ⟨⟨21/128, 231/640⟩, 3/1280⟩
def center3795 : GaussianRat :=
  ⟨32322943/250000000, 63381939/250000000⟩
def contact3795 : RatBall := localContactBall tau3795 center3795
def work3795 : RoundedTauEval :=
  evalTau precision tau3795 contact3795 logTwoBall

theorem center_sq3795 : (center3795.re : ℝ)^2 +
    (center3795.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3795]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3795 : work3795.theta.ok = true ∧
    work3795.jac.invOK = true ∧ acceptsUnitSq work3795.out = true := by
  norm_num [work3795, contact3795, tau3795, center3795, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3795 : CellCertificate where
  tauBall := tau3795
  contactCenter := center3795
  contactBall := contact3795
  work := work3795
  center_sq := center_sq3795
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3795.1
  jac_ok := checks3795.2.1
  accepted := checks3795.2.2

def tau3796 : RatBall :=
  ⟨⟨107/640, 231/640⟩, 3/1280⟩
def center3796 : GaussianRat :=
  ⟨65835777/500000000, 253197689/1000000000⟩
def contact3796 : RatBall := localContactBall tau3796 center3796
def work3796 : RoundedTauEval :=
  evalTau precision tau3796 contact3796 logTwoBall

theorem center_sq3796 : (center3796.re : ℝ)^2 +
    (center3796.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3796]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3796 : work3796.theta.ok = true ∧
    work3796.jac.invOK = true ∧ acceptsUnitSq work3796.out = true := by
  norm_num [work3796, contact3796, tau3796, center3796, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3796 : CellCertificate where
  tauBall := tau3796
  contactCenter := center3796
  contactBall := contact3796
  work := work3796
  center_sq := center_sq3796
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3796.1
  jac_ok := checks3796.2.1
  accepted := checks3796.2.2

def tau3797 : RatBall :=
  ⟨⟨109/640, 229/640⟩, 3/1280⟩
def center3797 : GaussianRat :=
  ⟨133711273/1000000000, 250491903/1000000000⟩
def contact3797 : RatBall := localContactBall tau3797 center3797
def work3797 : RoundedTauEval :=
  evalTau precision tau3797 contact3797 logTwoBall

theorem center_sq3797 : (center3797.re : ℝ)^2 +
    (center3797.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3797]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3797 : work3797.theta.ok = true ∧
    work3797.jac.invOK = true ∧ acceptsUnitSq work3797.out = true := by
  norm_num [work3797, contact3797, tau3797, center3797, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3797 : CellCertificate where
  tauBall := tau3797
  contactCenter := center3797
  contactBall := contact3797
  work := work3797
  center_sq := center_sq3797
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3797.1
  jac_ok := checks3797.2.1
  accepted := checks3797.2.2

def tau3798 : RatBall :=
  ⟨⟨111/640, 229/640⟩, 3/1280⟩
def center3798 : GaussianRat :=
  ⟨136076987/1000000000, 250155999/1000000000⟩
def contact3798 : RatBall := localContactBall tau3798 center3798
def work3798 : RoundedTauEval :=
  evalTau precision tau3798 contact3798 logTwoBall

theorem center_sq3798 : (center3798.re : ℝ)^2 +
    (center3798.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3798]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3798 : work3798.theta.ok = true ∧
    work3798.jac.invOK = true ∧ acceptsUnitSq work3798.out = true := by
  norm_num [work3798, contact3798, tau3798, center3798, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3798 : CellCertificate where
  tauBall := tau3798
  contactCenter := center3798
  contactBall := contact3798
  work := work3798
  center_sq := center_sq3798
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3798.1
  jac_ok := checks3798.2.1
  accepted := checks3798.2.2

def tau3799 : RatBall :=
  ⟨⟨109/640, 231/640⟩, 3/1280⟩
def center3799 : GaussianRat :=
  ⟨134046881/1000000000, 15803901/62500000⟩
def contact3799 : RatBall := localContactBall tau3799 center3799
def work3799 : RoundedTauEval :=
  evalTau precision tau3799 contact3799 logTwoBall

theorem center_sq3799 : (center3799.re : ℝ)^2 +
    (center3799.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3799]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3799 : work3799.theta.ok = true ∧
    work3799.jac.invOK = true ∧ acceptsUnitSq work3799.out = true := by
  norm_num [work3799, contact3799, tau3799, center3799, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3799 : CellCertificate where
  tauBall := tau3799
  contactCenter := center3799
  contactBall := contact3799
  work := work3799
  center_sq := center_sq3799
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3799.1
  jac_ok := checks3799.2.1
  accepted := checks3799.2.2

def cells : List CellCertificate := [cell3792, cell3793, cell3794, cell3795, cell3796, cell3797, cell3798, cell3799]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474
