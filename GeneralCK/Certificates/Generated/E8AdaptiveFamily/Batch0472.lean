import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0472

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3776 : RatBall :=
  ⟨⟨81/640, 243/640⟩, 3/1280⟩
def center3776 : GaussianRat :=
  ⟨51020881/500000000, 135875479/500000000⟩
def contact3776 : RatBall := localContactBall tau3776 center3776
def work3776 : RoundedTauEval :=
  evalTau precision tau3776 contact3776 logTwoBall

theorem center_sq3776 : (center3776.re : ℝ)^2 +
    (center3776.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3776]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3776 : work3776.theta.ok = true ∧
    work3776.jac.invOK = true ∧ acceptsUnitSq work3776.out = true := by
  norm_num [work3776, contact3776, tau3776, center3776, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3776 : CellCertificate where
  tauBall := tau3776
  contactCenter := center3776
  contactBall := contact3776
  work := work3776
  center_sq := center_sq3776
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3776.1
  jac_ok := checks3776.2.1
  accepted := checks3776.2.2

def tau3777 : RatBall :=
  ⟨⟨83/640, 243/640⟩, 3/1280⟩
def center3777 : GaussianRat :=
  ⟨4180239/40000000, 271464801/1000000000⟩
def contact3777 : RatBall := localContactBall tau3777 center3777
def work3777 : RoundedTauEval :=
  evalTau precision tau3777 contact3777 logTwoBall

theorem center_sq3777 : (center3777.re : ℝ)^2 +
    (center3777.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3777]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3777 : work3777.theta.ok = true ∧
    work3777.jac.invOK = true ∧ acceptsUnitSq work3777.out = true := by
  norm_num [work3777, contact3777, tau3777, center3777, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3777 : CellCertificate where
  tauBall := tau3777
  contactCenter := center3777
  contactBall := contact3777
  work := work3777
  center_sq := center_sq3777
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3777.1
  jac_ok := checks3777.2.1
  accepted := checks3777.2.2

def tau3778 : RatBall :=
  ⟨⟨17/128, 241/640⟩, 3/1280⟩
def center3778 : GaussianRat :=
  ⟨53336381/500000000, 268717167/1000000000⟩
def contact3778 : RatBall := localContactBall tau3778 center3778
def work3778 : RoundedTauEval :=
  evalTau precision tau3778 contact3778 logTwoBall

theorem center_sq3778 : (center3778.re : ℝ)^2 +
    (center3778.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3778]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3778 : work3778.theta.ok = true ∧
    work3778.jac.invOK = true ∧ acceptsUnitSq work3778.out = true := by
  norm_num [work3778, contact3778, tau3778, center3778, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3778 : CellCertificate where
  tauBall := tau3778
  contactCenter := center3778
  contactBall := contact3778
  work := work3778
  center_sq := center_sq3778
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3778.1
  jac_ok := checks3778.2.1
  accepted := checks3778.2.2

def tau3779 : RatBall :=
  ⟨⟨87/640, 241/640⟩, 3/1280⟩
def center3779 : GaussianRat :=
  ⟨109122947/1000000000, 53684517/200000000⟩
def contact3779 : RatBall := localContactBall tau3779 center3779
def work3779 : RoundedTauEval :=
  evalTau precision tau3779 contact3779 logTwoBall

theorem center_sq3779 : (center3779.re : ℝ)^2 +
    (center3779.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3779]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3779 : work3779.theta.ok = true ∧
    work3779.jac.invOK = true ∧ acceptsUnitSq work3779.out = true := by
  norm_num [work3779, contact3779, tau3779, center3779, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3779 : CellCertificate where
  tauBall := tau3779
  contactCenter := center3779
  contactBall := contact3779
  work := work3779
  center_sq := center_sq3779
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3779.1
  jac_ok := checks3779.2.1
  accepted := checks3779.2.2

def tau3780 : RatBall :=
  ⟨⟨89/640, 241/640⟩, 3/1280⟩
def center3780 : GaussianRat :=
  ⟨22313823/200000000, 13406097/50000000⟩
def contact3780 : RatBall := localContactBall tau3780 center3780
def work3780 : RoundedTauEval :=
  evalTau precision tau3780 contact3780 logTwoBall

theorem center_sq3780 : (center3780.re : ℝ)^2 +
    (center3780.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3780]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3780 : work3780.theta.ok = true ∧
    work3780.jac.invOK = true ∧ acceptsUnitSq work3780.out = true := by
  norm_num [work3780, contact3780, tau3780, center3780, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3780 : CellCertificate where
  tauBall := tau3780
  contactCenter := center3780
  contactBall := contact3780
  work := work3780
  center_sq := center_sq3780
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3780.1
  jac_ok := checks3780.2.1
  accepted := checks3780.2.2

def tau3781 : RatBall :=
  ⟨⟨97/640, 229/640⟩, 3/1280⟩
def center3781 : GaussianRat :=
  ⟨119425411/1000000000, 252398639/1000000000⟩
def contact3781 : RatBall := localContactBall tau3781 center3781
def work3781 : RoundedTauEval :=
  evalTau precision tau3781 contact3781 logTwoBall

theorem center_sq3781 : (center3781.re : ℝ)^2 +
    (center3781.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3781]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3781 : work3781.theta.ok = true ∧
    work3781.jac.invOK = true ∧ acceptsUnitSq work3781.out = true := by
  norm_num [work3781, contact3781, tau3781, center3781, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3781 : CellCertificate where
  tauBall := tau3781
  contactCenter := center3781
  contactBall := contact3781
  work := work3781
  center_sq := center_sq3781
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3781.1
  jac_ok := checks3781.2.1
  accepted := checks3781.2.2

def tau3782 : RatBall :=
  ⟨⟨99/640, 229/640⟩, 3/1280⟩
def center3782 : GaussianRat :=
  ⟨30454243/250000000, 126047019/500000000⟩
def contact3782 : RatBall := localContactBall tau3782 center3782
def work3782 : RoundedTauEval :=
  evalTau precision tau3782 contact3782 logTwoBall

theorem center_sq3782 : (center3782.re : ℝ)^2 +
    (center3782.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3782]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3782 : work3782.theta.ok = true ∧
    work3782.jac.invOK = true ∧ acceptsUnitSq work3782.out = true := by
  norm_num [work3782, contact3782, tau3782, center3782, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3782 : CellCertificate where
  tauBall := tau3782
  contactCenter := center3782
  contactBall := contact3782
  work := work3782
  center_sq := center_sq3782
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3782.1
  jac_ok := checks3782.2.1
  accepted := checks3782.2.2

def tau3783 : RatBall :=
  ⟨⟨97/640, 231/640⟩, 3/1280⟩
def center3783 : GaussianRat :=
  ⟨59864687/500000000, 254794957/1000000000⟩
def contact3783 : RatBall := localContactBall tau3783 center3783
def work3783 : RoundedTauEval :=
  evalTau precision tau3783 contact3783 logTwoBall

theorem center_sq3783 : (center3783.re : ℝ)^2 +
    (center3783.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3783]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3783 : work3783.theta.ok = true ∧
    work3783.jac.invOK = true ∧ acceptsUnitSq work3783.out = true := by
  norm_num [work3783, contact3783, tau3783, center3783, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3783 : CellCertificate where
  tauBall := tau3783
  contactCenter := center3783
  contactBall := contact3783
  work := work3783
  center_sq := center_sq3783
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3783.1
  jac_ok := checks3783.2.1
  accepted := checks3783.2.2

def cells : List CellCertificate := [cell3776, cell3777, cell3778, cell3779, cell3780, cell3781, cell3782, cell3783]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0472
