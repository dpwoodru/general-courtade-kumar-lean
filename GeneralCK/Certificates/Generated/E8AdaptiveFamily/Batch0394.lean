import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3152 : RatBall :=
  ⟨⟨101/640, -229/640⟩, 3/1280⟩
def center3152 : GaussianRat :=
  ⟨62102193/500000000, -7868253/31250000⟩
def contact3152 : RatBall := localContactBall tau3152 center3152
def work3152 : RoundedTauEval :=
  evalTau precision tau3152 contact3152 logTwoBall

theorem center_sq3152 : (center3152.re : ℝ)^2 +
    (center3152.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3152]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3152 : work3152.theta.ok = true ∧
    work3152.jac.invOK = true ∧ acceptsUnitSq work3152.out = true := by
  norm_num [work3152, contact3152, tau3152, center3152, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3152 : CellCertificate where
  tauBall := tau3152
  contactCenter := center3152
  contactBall := contact3152
  work := work3152
  center_sq := center_sq3152
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3152.1
  jac_ok := checks3152.2.1
  accepted := checks3152.2.2

def tau3153 : RatBall :=
  ⟨⟨103/640, -229/640⟩, 3/1280⟩
def center3153 : GaussianRat :=
  ⟨126587587/1000000000, -125734431/500000000⟩
def contact3153 : RatBall := localContactBall tau3153 center3153
def work3153 : RoundedTauEval :=
  evalTau precision tau3153 contact3153 logTwoBall

theorem center_sq3153 : (center3153.re : ℝ)^2 +
    (center3153.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3153]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3153 : work3153.theta.ok = true ∧
    work3153.jac.invOK = true ∧ acceptsUnitSq work3153.out = true := by
  norm_num [work3153, contact3153, tau3153, center3153, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3153 : CellCertificate where
  tauBall := tau3153
  contactCenter := center3153
  contactBall := contact3153
  work := work3153
  center_sq := center_sq3153
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3153.1
  jac_ok := checks3153.2.1
  accepted := checks3153.2.2

def tau3154 : RatBall :=
  ⟨⟨21/128, -231/640⟩, 3/1280⟩
def center3154 : GaussianRat :=
  ⟨32322943/250000000, -63381939/250000000⟩
def contact3154 : RatBall := localContactBall tau3154 center3154
def work3154 : RoundedTauEval :=
  evalTau precision tau3154 contact3154 logTwoBall

theorem center_sq3154 : (center3154.re : ℝ)^2 +
    (center3154.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3154]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3154 : work3154.theta.ok = true ∧
    work3154.jac.invOK = true ∧ acceptsUnitSq work3154.out = true := by
  norm_num [work3154, contact3154, tau3154, center3154, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3154 : CellCertificate where
  tauBall := tau3154
  contactCenter := center3154
  contactBall := contact3154
  work := work3154
  center_sq := center_sq3154
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3154.1
  jac_ok := checks3154.2.1
  accepted := checks3154.2.2

def tau3155 : RatBall :=
  ⟨⟨107/640, -231/640⟩, 3/1280⟩
def center3155 : GaussianRat :=
  ⟨65835777/500000000, -253197689/1000000000⟩
def contact3155 : RatBall := localContactBall tau3155 center3155
def work3155 : RoundedTauEval :=
  evalTau precision tau3155 contact3155 logTwoBall

theorem center_sq3155 : (center3155.re : ℝ)^2 +
    (center3155.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3155]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3155 : work3155.theta.ok = true ∧
    work3155.jac.invOK = true ∧ acceptsUnitSq work3155.out = true := by
  norm_num [work3155, contact3155, tau3155, center3155, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3155 : CellCertificate where
  tauBall := tau3155
  contactCenter := center3155
  contactBall := contact3155
  work := work3155
  center_sq := center_sq3155
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3155.1
  jac_ok := checks3155.2.1
  accepted := checks3155.2.2

def tau3156 : RatBall :=
  ⟨⟨21/128, -229/640⟩, 3/1280⟩
def center3156 : GaussianRat :=
  ⟨128966511/1000000000, -50229677/200000000⟩
def contact3156 : RatBall := localContactBall tau3156 center3156
def work3156 : RoundedTauEval :=
  evalTau precision tau3156 contact3156 logTwoBall

theorem center_sq3156 : (center3156.re : ℝ)^2 +
    (center3156.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3156]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3156 : work3156.theta.ok = true ∧
    work3156.jac.invOK = true ∧ acceptsUnitSq work3156.out = true := by
  norm_num [work3156, contact3156, tau3156, center3156, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3156 : CellCertificate where
  tauBall := tau3156
  contactCenter := center3156
  contactBall := contact3156
  work := work3156
  center_sq := center_sq3156
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3156.1
  jac_ok := checks3156.2.1
  accepted := checks3156.2.2

def tau3157 : RatBall :=
  ⟨⟨107/640, -229/640⟩, 3/1280⟩
def center3157 : GaussianRat :=
  ⟨65670547/500000000, -62705679/250000000⟩
def contact3157 : RatBall := localContactBall tau3157 center3157
def work3157 : RoundedTauEval :=
  evalTau precision tau3157 contact3157 logTwoBall

theorem center_sq3157 : (center3157.re : ℝ)^2 +
    (center3157.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3157]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3157 : work3157.theta.ok = true ∧
    work3157.jac.invOK = true ∧ acceptsUnitSq work3157.out = true := by
  norm_num [work3157, contact3157, tau3157, center3157, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3157 : CellCertificate where
  tauBall := tau3157
  contactCenter := center3157
  contactBall := contact3157
  work := work3157
  center_sq := center_sq3157
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3157.1
  jac_ok := checks3157.2.1
  accepted := checks3157.2.2

def tau3158 : RatBall :=
  ⟨⟨109/640, -231/640⟩, 3/1280⟩
def center3158 : GaussianRat :=
  ⟨134046881/1000000000, -15803901/62500000⟩
def contact3158 : RatBall := localContactBall tau3158 center3158
def work3158 : RoundedTauEval :=
  evalTau precision tau3158 contact3158 logTwoBall

theorem center_sq3158 : (center3158.re : ℝ)^2 +
    (center3158.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3158]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3158 : work3158.theta.ok = true ∧
    work3158.jac.invOK = true ∧ acceptsUnitSq work3158.out = true := by
  norm_num [work3158, contact3158, tau3158, center3158, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3158 : CellCertificate where
  tauBall := tau3158
  contactCenter := center3158
  contactBall := contact3158
  work := work3158
  center_sq := center_sq3158
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3158.1
  jac_ok := checks3158.2.1
  accepted := checks3158.2.2

def tau3159 : RatBall :=
  ⟨⟨111/640, -231/640⟩, 3/1280⟩
def center3159 : GaussianRat :=
  ⟨34104423/250000000, -25252199/100000000⟩
def contact3159 : RatBall := localContactBall tau3159 center3159
def work3159 : RoundedTauEval :=
  evalTau precision tau3159 contact3159 logTwoBall

theorem center_sq3159 : (center3159.re : ℝ)^2 +
    (center3159.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3159]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3159 : work3159.theta.ok = true ∧
    work3159.jac.invOK = true ∧ acceptsUnitSq work3159.out = true := by
  norm_num [work3159, contact3159, tau3159, center3159, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3159 : CellCertificate where
  tauBall := tau3159
  contactCenter := center3159
  contactBall := contact3159
  work := work3159
  center_sq := center_sq3159
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3159.1
  jac_ok := checks3159.2.1
  accepted := checks3159.2.2

def cells : List CellCertificate := [cell3152, cell3153, cell3154, cell3155, cell3156, cell3157, cell3158, cell3159]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394
