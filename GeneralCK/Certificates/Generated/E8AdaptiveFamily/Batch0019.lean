import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0152 : RatBall :=
  ⟨⟨11/80, -13/80⟩, 3/160⟩
def center0152 : GaussianRat :=
  ⟨48637291/500000000, -111393603/1000000000⟩
def contact0152 : RatBall := localContactBall tau0152 center0152
def work0152 : RoundedTauEval :=
  evalTau precision tau0152 contact0152 logTwoBall

theorem center_sq0152 : (center0152.re : ℝ)^2 +
    (center0152.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0152]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0152 : work0152.theta.ok = true ∧
    work0152.jac.invOK = true ∧ acceptsUnitSq work0152.out = true := by
  norm_num [work0152, contact0152, tau0152, center0152, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0152 : CellCertificate where
  tauBall := tau0152
  contactCenter := center0152
  contactBall := contact0152
  work := work0152
  center_sq := center_sq0152
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0152.1
  jac_ok := checks0152.2.1
  accepted := checks0152.2.2

def tau0153 : RatBall :=
  ⟨⟨13/80, -3/16⟩, 3/160⟩
def center0153 : GaussianRat :=
  ⟨115659239/1000000000, -127856533/1000000000⟩
def contact0153 : RatBall := localContactBall tau0153 center0153
def work0153 : RoundedTauEval :=
  evalTau precision tau0153 contact0153 logTwoBall

theorem center_sq0153 : (center0153.re : ℝ)^2 +
    (center0153.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0153]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0153 : work0153.theta.ok = true ∧
    work0153.jac.invOK = true ∧ acceptsUnitSq work0153.out = true := by
  norm_num [work0153, contact0153, tau0153, center0153, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0153 : CellCertificate where
  tauBall := tau0153
  contactCenter := center0153
  contactBall := contact0153
  work := work0153
  center_sq := center_sq0153
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0153.1
  jac_ok := checks0153.2.1
  accepted := checks0153.2.2

def tau0154 : RatBall :=
  ⟨⟨3/16, -3/16⟩, 3/160⟩
def center0154 : GaussianRat :=
  ⟨132989007/1000000000, -15833617/125000000⟩
def contact0154 : RatBall := localContactBall tau0154 center0154
def work0154 : RoundedTauEval :=
  evalTau precision tau0154 contact0154 logTwoBall

theorem center_sq0154 : (center0154.re : ℝ)^2 +
    (center0154.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0154]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0154 : work0154.theta.ok = true ∧
    work0154.jac.invOK = true ∧ acceptsUnitSq work0154.out = true := by
  norm_num [work0154, contact0154, tau0154, center0154, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0154 : CellCertificate where
  tauBall := tau0154
  contactCenter := center0154
  contactBall := contact0154
  work := work0154
  center_sq := center_sq0154
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0154.1
  jac_ok := checks0154.2.1
  accepted := checks0154.2.2

def tau0155 : RatBall :=
  ⟨⟨13/80, -13/80⟩, 3/160⟩
def center0155 : GaussianRat :=
  ⟨114628827/1000000000, -110510723/1000000000⟩
def contact0155 : RatBall := localContactBall tau0155 center0155
def work0155 : RoundedTauEval :=
  evalTau precision tau0155 contact0155 logTwoBall

theorem center_sq0155 : (center0155.re : ℝ)^2 +
    (center0155.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0155]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0155 : work0155.theta.ok = true ∧
    work0155.jac.invOK = true ∧ acceptsUnitSq work0155.out = true := by
  norm_num [work0155, contact0155, tau0155, center0155, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0155 : CellCertificate where
  tauBall := tau0155
  contactCenter := center0155
  contactBall := contact0155
  work := work0155
  center_sq := center_sq0155
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0155.1
  jac_ok := checks0155.2.1
  accepted := checks0155.2.2

def tau0156 : RatBall :=
  ⟨⟨3/16, -13/80⟩, 3/160⟩
def center0156 : GaussianRat :=
  ⟨131822371/1000000000, -13687313/125000000⟩
def contact0156 : RatBall := localContactBall tau0156 center0156
def work0156 : RoundedTauEval :=
  evalTau precision tau0156 contact0156 logTwoBall

theorem center_sq0156 : (center0156.re : ℝ)^2 +
    (center0156.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0156]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0156 : work0156.theta.ok = true ∧
    work0156.jac.invOK = true ∧ acceptsUnitSq work0156.out = true := by
  norm_num [work0156, contact0156, tau0156, center0156, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0156 : CellCertificate where
  tauBall := tau0156
  contactCenter := center0156
  contactBall := contact0156
  work := work0156
  center_sq := center_sq0156
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0156.1
  jac_ok := checks0156.2.1
  accepted := checks0156.2.2

def tau0157 : RatBall :=
  ⟨⟨13/80, -11/80⟩, 3/160⟩
def center0157 : GaussianRat :=
  ⟨22751869/200000000, -46647191/500000000⟩
def contact0157 : RatBall := localContactBall tau0157 center0157
def work0157 : RoundedTauEval :=
  evalTau precision tau0157 contact0157 logTwoBall

theorem center_sq0157 : (center0157.re : ℝ)^2 +
    (center0157.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0157]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0157 : work0157.theta.ok = true ∧
    work0157.jac.invOK = true ∧ acceptsUnitSq work0157.out = true := by
  norm_num [work0157, contact0157, tau0157, center0157, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0157 : CellCertificate where
  tauBall := tau0157
  contactCenter := center0157
  contactBall := contact0157
  work := work0157
  center_sq := center_sq0157
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0157.1
  jac_ok := checks0157.2.1
  accepted := checks0157.2.2

def tau0158 : RatBall :=
  ⟨⟨3/16, -11/80⟩, 3/160⟩
def center0158 : GaussianRat :=
  ⟨130837509/1000000000, -92449971/1000000000⟩
def contact0158 : RatBall := localContactBall tau0158 center0158
def work0158 : RoundedTauEval :=
  evalTau precision tau0158 contact0158 logTwoBall

theorem center_sq0158 : (center0158.re : ℝ)^2 +
    (center0158.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0158]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0158 : work0158.theta.ok = true ∧
    work0158.jac.invOK = true ∧ acceptsUnitSq work0158.out = true := by
  norm_num [work0158, contact0158, tau0158, center0158, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0158 : CellCertificate where
  tauBall := tau0158
  contactCenter := center0158
  contactBall := contact0158
  work := work0158
  center_sq := center_sq0158
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0158.1
  jac_ok := checks0158.2.1
  accepted := checks0158.2.2

def tau0159 : RatBall :=
  ⟨⟨13/80, -9/80⟩, 3/160⟩
def center0159 : GaussianRat :=
  ⟨56522129/500000000, -76186323/1000000000⟩
def contact0159 : RatBall := localContactBall tau0159 center0159
def work0159 : RoundedTauEval :=
  evalTau precision tau0159 contact0159 logTwoBall

theorem center_sq0159 : (center0159.re : ℝ)^2 +
    (center0159.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0159]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0159 : work0159.theta.ok = true ∧
    work0159.jac.invOK = true ∧ acceptsUnitSq work0159.out = true := by
  norm_num [work0159, contact0159, tau0159, center0159, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0159 : CellCertificate where
  tauBall := tau0159
  contactCenter := center0159
  contactBall := contact0159
  work := work0159
  center_sq := center_sq0159
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0159.1
  jac_ok := checks0159.2.1
  accepted := checks0159.2.2

def cells : List CellCertificate := [cell0152, cell0153, cell0154, cell0155, cell0156, cell0157, cell0158, cell0159]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019
