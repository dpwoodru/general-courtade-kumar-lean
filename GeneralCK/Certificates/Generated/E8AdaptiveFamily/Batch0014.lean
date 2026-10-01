import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0112 : RatBall :=
  ⟨⟨-13/80, -13/80⟩, 3/160⟩
def center0112 : GaussianRat :=
  ⟨-114628827/1000000000, -110510723/1000000000⟩
def contact0112 : RatBall := localContactBall tau0112 center0112
def work0112 : RoundedTauEval :=
  evalTau precision tau0112 contact0112 logTwoBall

theorem center_sq0112 : (center0112.re : ℝ)^2 +
    (center0112.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0112]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0112 : work0112.theta.ok = true ∧
    work0112.jac.invOK = true ∧ acceptsUnitSq work0112.out = true := by
  norm_num [work0112, contact0112, tau0112, center0112, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0112 : CellCertificate where
  tauBall := tau0112
  contactCenter := center0112
  contactBall := contact0112
  work := work0112
  center_sq := center_sq0112
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0112.1
  jac_ok := checks0112.2.1
  accepted := checks0112.2.2

def tau0113 : RatBall :=
  ⟨⟨-11/80, -3/16⟩, 3/160⟩
def center0113 : GaussianRat :=
  ⟨-1227011/12500000, -8055803/62500000⟩
def contact0113 : RatBall := localContactBall tau0113 center0113
def work0113 : RoundedTauEval :=
  evalTau precision tau0113 contact0113 logTwoBall

theorem center_sq0113 : (center0113.re : ℝ)^2 +
    (center0113.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0113]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0113 : work0113.theta.ok = true ∧
    work0113.jac.invOK = true ∧ acceptsUnitSq work0113.out = true := by
  norm_num [work0113, contact0113, tau0113, center0113, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0113 : CellCertificate where
  tauBall := tau0113
  contactCenter := center0113
  contactBall := contact0113
  work := work0113
  center_sq := center_sq0113
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0113.1
  jac_ok := checks0113.2.1
  accepted := checks0113.2.2

def tau0114 : RatBall :=
  ⟨⟨-9/80, -3/16⟩, 3/160⟩
def center0114 : GaussianRat :=
  ⟨-80517041/1000000000, -8110609/62500000⟩
def contact0114 : RatBall := localContactBall tau0114 center0114
def work0114 : RoundedTauEval :=
  evalTau precision tau0114 contact0114 logTwoBall

theorem center_sq0114 : (center0114.re : ℝ)^2 +
    (center0114.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0114]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0114 : work0114.theta.ok = true ∧
    work0114.jac.invOK = true ∧ acceptsUnitSq work0114.out = true := by
  norm_num [work0114, contact0114, tau0114, center0114, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0114 : CellCertificate where
  tauBall := tau0114
  contactCenter := center0114
  contactBall := contact0114
  work := work0114
  center_sq := center_sq0114
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0114.1
  jac_ok := checks0114.2.1
  accepted := checks0114.2.2

def tau0115 : RatBall :=
  ⟨⟨-11/80, -13/80⟩, 3/160⟩
def center0115 : GaussianRat :=
  ⟨-48637291/500000000, -111393603/1000000000⟩
def contact0115 : RatBall := localContactBall tau0115 center0115
def work0115 : RoundedTauEval :=
  evalTau precision tau0115 contact0115 logTwoBall

theorem center_sq0115 : (center0115.re : ℝ)^2 +
    (center0115.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0115]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0115 : work0115.theta.ok = true ∧
    work0115.jac.invOK = true ∧ acceptsUnitSq work0115.out = true := by
  norm_num [work0115, contact0115, tau0115, center0115, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0115 : CellCertificate where
  tauBall := tau0115
  contactCenter := center0115
  contactBall := contact0115
  work := work0115
  center_sq := center_sq0115
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0115.1
  jac_ok := checks0115.2.1
  accepted := checks0115.2.2

def tau0116 : RatBall :=
  ⟨⟨-9/80, -13/80⟩, 3/160⟩
def center0116 : GaussianRat :=
  ⟨-79781827/1000000000, -56070187/500000000⟩
def contact0116 : RatBall := localContactBall tau0116 center0116
def work0116 : RoundedTauEval :=
  evalTau precision tau0116 contact0116 logTwoBall

theorem center_sq0116 : (center0116.re : ℝ)^2 +
    (center0116.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0116]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0116 : work0116.theta.ok = true ∧
    work0116.jac.invOK = true ∧ acceptsUnitSq work0116.out = true := by
  norm_num [work0116, contact0116, tau0116, center0116, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0116 : CellCertificate where
  tauBall := tau0116
  contactCenter := center0116
  contactBall := contact0116
  work := work0116
  center_sq := center_sq0116
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0116.1
  jac_ok := checks0116.2.1
  accepted := checks0116.2.2

def tau0117 : RatBall :=
  ⟨⟨-3/16, -11/80⟩, 3/160⟩
def center0117 : GaussianRat :=
  ⟨-130837509/1000000000, -92449971/1000000000⟩
def contact0117 : RatBall := localContactBall tau0117 center0117
def work0117 : RoundedTauEval :=
  evalTau precision tau0117 contact0117 logTwoBall

theorem center_sq0117 : (center0117.re : ℝ)^2 +
    (center0117.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0117]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0117 : work0117.theta.ok = true ∧
    work0117.jac.invOK = true ∧ acceptsUnitSq work0117.out = true := by
  norm_num [work0117, contact0117, tau0117, center0117, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0117 : CellCertificate where
  tauBall := tau0117
  contactCenter := center0117
  contactBall := contact0117
  work := work0117
  center_sq := center_sq0117
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0117.1
  jac_ok := checks0117.2.1
  accepted := checks0117.2.2

def tau0118 : RatBall :=
  ⟨⟨-13/80, -11/80⟩, 3/160⟩
def center0118 : GaussianRat :=
  ⟨-22751869/200000000, -46647191/500000000⟩
def contact0118 : RatBall := localContactBall tau0118 center0118
def work0118 : RoundedTauEval :=
  evalTau precision tau0118 contact0118 logTwoBall

theorem center_sq0118 : (center0118.re : ℝ)^2 +
    (center0118.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0118]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0118 : work0118.theta.ok = true ∧
    work0118.jac.invOK = true ∧ acceptsUnitSq work0118.out = true := by
  norm_num [work0118, contact0118, tau0118, center0118, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0118 : CellCertificate where
  tauBall := tau0118
  contactCenter := center0118
  contactBall := contact0118
  work := work0118
  center_sq := center_sq0118
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0118.1
  jac_ok := checks0118.2.1
  accepted := checks0118.2.2

def tau0119 : RatBall :=
  ⟨⟨-3/16, -9/80⟩, 3/160⟩
def center0119 : GaussianRat :=
  ⟨-26005447/200000000, -37751763/500000000⟩
def contact0119 : RatBall := localContactBall tau0119 center0119
def work0119 : RoundedTauEval :=
  evalTau precision tau0119 contact0119 logTwoBall

theorem center_sq0119 : (center0119.re : ℝ)^2 +
    (center0119.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0119]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0119 : work0119.theta.ok = true ∧
    work0119.jac.invOK = true ∧ acceptsUnitSq work0119.out = true := by
  norm_num [work0119, contact0119, tau0119, center0119, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0119 : CellCertificate where
  tauBall := tau0119
  contactCenter := center0119
  contactBall := contact0119
  work := work0119
  center_sq := center_sq0119
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0119.1
  jac_ok := checks0119.2.1
  accepted := checks0119.2.2

def cells : List CellCertificate := [cell0112, cell0113, cell0114, cell0115, cell0116, cell0117, cell0118, cell0119]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014
