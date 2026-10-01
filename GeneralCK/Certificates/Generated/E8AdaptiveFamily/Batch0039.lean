import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0312 : RatBall :=
  ⟨⟨19/80, 9/80⟩, 3/160⟩
def center0312 : GaussianRat :=
  ⟨163469111/1000000000, 36947527/500000000⟩
def contact0312 : RatBall := localContactBall tau0312 center0312
def work0312 : RoundedTauEval :=
  evalTau precision tau0312 contact0312 logTwoBall

theorem center_sq0312 : (center0312.re : ℝ)^2 +
    (center0312.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0312]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0312 : work0312.theta.ok = true ∧
    work0312.jac.invOK = true ∧ acceptsUnitSq work0312.out = true := by
  norm_num [work0312, contact0312, tau0312, center0312, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0312 : CellCertificate where
  tauBall := tau0312
  contactCenter := center0312
  contactBall := contact0312
  work := work0312
  center_sq := center_sq0312
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0312.1
  jac_ok := checks0312.2.1
  accepted := checks0312.2.2

def tau0313 : RatBall :=
  ⟨⟨17/80, 11/80⟩, 3/160⟩
def center0313 : GaussianRat :=
  ⟨1154229/7812500, 91503559/1000000000⟩
def contact0313 : RatBall := localContactBall tau0313 center0313
def work0313 : RoundedTauEval :=
  evalTau precision tau0313 contact0313 logTwoBall

theorem center_sq0313 : (center0313.re : ℝ)^2 +
    (center0313.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0313]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0313 : work0313.theta.ok = true ∧
    work0313.jac.invOK = true ∧ acceptsUnitSq work0313.out = true := by
  norm_num [work0313, contact0313, tau0313, center0313, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0313 : CellCertificate where
  tauBall := tau0313
  contactCenter := center0313
  contactBall := contact0313
  work := work0313
  center_sq := center_sq0313
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0313.1
  jac_ok := checks0313.2.1
  accepted := checks0313.2.2

def tau0314 : RatBall :=
  ⟨⟨19/80, 11/80⟩, 3/160⟩
def center0314 : GaussianRat :=
  ⟨82225973/500000000, 18092371/200000000⟩
def contact0314 : RatBall := localContactBall tau0314 center0314
def work0314 : RoundedTauEval :=
  evalTau precision tau0314 contact0314 logTwoBall

theorem center_sq0314 : (center0314.re : ℝ)^2 +
    (center0314.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0314]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0314 : work0314.theta.ok = true ∧
    work0314.jac.invOK = true ∧ acceptsUnitSq work0314.out = true := by
  norm_num [work0314, contact0314, tau0314, center0314, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0314 : CellCertificate where
  tauBall := tau0314
  contactCenter := center0314
  contactBall := contact0314
  work := work0314
  center_sq := center_sq0314
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0314.1
  jac_ok := checks0314.2.1
  accepted := checks0314.2.2

def tau0315 : RatBall :=
  ⟨⟨21/80, 9/80⟩, 3/160⟩
def center0315 : GaussianRat :=
  ⟨44973153/250000000, 72980409/1000000000⟩
def contact0315 : RatBall := localContactBall tau0315 center0315
def work0315 : RoundedTauEval :=
  evalTau precision tau0315 contact0315 logTwoBall

theorem center_sq0315 : (center0315.re : ℝ)^2 +
    (center0315.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0315]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0315 : work0315.theta.ok = true ∧
    work0315.jac.invOK = true ∧ acceptsUnitSq work0315.out = true := by
  norm_num [work0315, contact0315, tau0315, center0315, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0315 : CellCertificate where
  tauBall := tau0315
  contactCenter := center0315
  contactBall := contact0315
  work := work0315
  center_sq := center_sq0315
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0315.1
  jac_ok := checks0315.2.1
  accepted := checks0315.2.2

def tau0316 : RatBall :=
  ⟨⟨23/80, 9/80⟩, 3/160⟩
def center0316 : GaussianRat :=
  ⟨196096551/1000000000, 71999991/1000000000⟩
def contact0316 : RatBall := localContactBall tau0316 center0316
def work0316 : RoundedTauEval :=
  evalTau precision tau0316 contact0316 logTwoBall

theorem center_sq0316 : (center0316.re : ℝ)^2 +
    (center0316.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0316]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0316 : work0316.theta.ok = true ∧
    work0316.jac.invOK = true ∧ acceptsUnitSq work0316.out = true := by
  norm_num [work0316, contact0316, tau0316, center0316, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0316 : CellCertificate where
  tauBall := tau0316
  contactCenter := center0316
  contactBall := contact0316
  work := work0316
  center_sq := center_sq0316
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0316.1
  jac_ok := checks0316.2.1
  accepted := checks0316.2.2

def tau0317 : RatBall :=
  ⟨⟨21/80, 11/80⟩, 3/160⟩
def center0317 : GaussianRat :=
  ⟨90476031/500000000, 89331987/1000000000⟩
def contact0317 : RatBall := localContactBall tau0317 center0317
def work0317 : RoundedTauEval :=
  evalTau precision tau0317 contact0317 logTwoBall

theorem center_sq0317 : (center0317.re : ℝ)^2 +
    (center0317.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0317]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0317 : work0317.theta.ok = true ∧
    work0317.jac.invOK = true ∧ acceptsUnitSq work0317.out = true := by
  norm_num [work0317, contact0317, tau0317, center0317, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0317 : CellCertificate where
  tauBall := tau0317
  contactCenter := center0317
  contactBall := contact0317
  work := work0317
  center_sq := center_sq0317
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0317.1
  jac_ok := checks0317.2.1
  accepted := checks0317.2.2

def tau0318 : RatBall :=
  ⟨⟨23/80, 11/80⟩, 3/160⟩
def center0318 : GaussianRat :=
  ⟨19722583/100000000, 88121387/1000000000⟩
def contact0318 : RatBall := localContactBall tau0318 center0318
def work0318 : RoundedTauEval :=
  evalTau precision tau0318 contact0318 logTwoBall

theorem center_sq0318 : (center0318.re : ℝ)^2 +
    (center0318.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0318]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0318 : work0318.theta.ok = true ∧
    work0318.jac.invOK = true ∧ acceptsUnitSq work0318.out = true := by
  norm_num [work0318, contact0318, tau0318, center0318, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0318 : CellCertificate where
  tauBall := tau0318
  contactCenter := center0318
  contactBall := contact0318
  work := work0318
  center_sq := center_sq0318
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0318.1
  jac_ok := checks0318.2.1
  accepted := checks0318.2.2

def tau0319 : RatBall :=
  ⟨⟨17/80, 13/80⟩, 3/160⟩
def center0319 : GaussianRat :=
  ⟨148834391/1000000000, 27091123/250000000⟩
def contact0319 : RatBall := localContactBall tau0319 center0319
def work0319 : RoundedTauEval :=
  evalTau precision tau0319 contact0319 logTwoBall

theorem center_sq0319 : (center0319.re : ℝ)^2 +
    (center0319.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0319]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0319 : work0319.theta.ok = true ∧
    work0319.jac.invOK = true ∧ acceptsUnitSq work0319.out = true := by
  norm_num [work0319, contact0319, tau0319, center0319, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0319 : CellCertificate where
  tauBall := tau0319
  contactCenter := center0319
  contactBall := contact0319
  work := work0319
  center_sq := center_sq0319
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0319.1
  jac_ok := checks0319.2.1
  accepted := checks0319.2.2

def cells : List CellCertificate := [cell0312, cell0313, cell0314, cell0315, cell0316, cell0317, cell0318, cell0319]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039
