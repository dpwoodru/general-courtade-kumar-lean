import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0344 : RatBall :=
  ⟨⟨-49/160, -37/160⟩, 3/320⟩
def center0344 : GaussianRat :=
  ⟨-8639819/40000000, -36909857/250000000⟩
def contact0344 : RatBall := localContactBall tau0344 center0344
def work0344 : RoundedTauEval :=
  evalTau precision tau0344 contact0344 logTwoBall

theorem center_sq0344 : (center0344.re : ℝ)^2 +
    (center0344.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0344]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0344 : work0344.theta.ok = true ∧
    work0344.jac.invOK = true ∧ acceptsUnitSq work0344.out = true := by
  norm_num [work0344, contact0344, tau0344, center0344, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0344 : CellCertificate where
  tauBall := tau0344
  contactCenter := center0344
  contactBall := contact0344
  work := work0344
  center_sq := center_sq0344
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0344.1
  jac_ok := checks0344.2.1
  accepted := checks0344.2.2

def tau0345 : RatBall :=
  ⟨⟨-53/160, -33/160⟩, 3/320⟩
def center0345 : GaussianRat :=
  ⟨-114945839/500000000, -32327639/250000000⟩
def contact0345 : RatBall := localContactBall tau0345 center0345
def work0345 : RoundedTauEval :=
  evalTau precision tau0345 contact0345 logTwoBall

theorem center_sq0345 : (center0345.re : ℝ)^2 +
    (center0345.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0345]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0345 : work0345.theta.ok = true ∧
    work0345.jac.invOK = true ∧ acceptsUnitSq work0345.out = true := by
  norm_num [work0345, contact0345, tau0345, center0345, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0345 : CellCertificate where
  tauBall := tau0345
  contactCenter := center0345
  contactBall := contact0345
  work := work0345
  center_sq := center_sq0345
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0345.1
  jac_ok := checks0345.2.1
  accepted := checks0345.2.2

def tau0346 : RatBall :=
  ⟨⟨-51/160, -7/32⟩, 3/320⟩
def center0346 : GaussianRat :=
  ⟨-111484361/500000000, -13840239/100000000⟩
def contact0346 : RatBall := localContactBall tau0346 center0346
def work0346 : RoundedTauEval :=
  evalTau precision tau0346 contact0346 logTwoBall

theorem center_sq0346 : (center0346.re : ℝ)^2 +
    (center0346.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0346]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0346 : work0346.theta.ok = true ∧
    work0346.jac.invOK = true ∧ acceptsUnitSq work0346.out = true := by
  norm_num [work0346, contact0346, tau0346, center0346, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0346 : CellCertificate where
  tauBall := tau0346
  contactCenter := center0346
  contactBall := contact0346
  work := work0346
  center_sq := center_sq0346
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0346.1
  jac_ok := checks0346.2.1
  accepted := checks0346.2.2

def tau0347 : RatBall :=
  ⟨⟨-49/160, -7/32⟩, 3/320⟩
def center0347 : GaussianRat :=
  ⟨-26859619/125000000, -139498183/1000000000⟩
def contact0347 : RatBall := localContactBall tau0347 center0347
def work0347 : RoundedTauEval :=
  evalTau precision tau0347 contact0347 logTwoBall

theorem center_sq0347 : (center0347.re : ℝ)^2 +
    (center0347.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0347 : work0347.theta.ok = true ∧
    work0347.jac.invOK = true ∧ acceptsUnitSq work0347.out = true := by
  norm_num [work0347, contact0347, tau0347, center0347, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0347 : CellCertificate where
  tauBall := tau0347
  contactCenter := center0347
  contactBall := contact0347
  work := work0347
  center_sq := center_sq0347
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0347.1
  jac_ok := checks0347.2.1
  accepted := checks0347.2.2

def tau0348 : RatBall :=
  ⟨⟨-51/160, -33/160⟩, 3/320⟩
def center0348 : GaussianRat :=
  ⟨-13868507/62500000, -13035901/100000000⟩
def contact0348 : RatBall := localContactBall tau0348 center0348
def work0348 : RoundedTauEval :=
  evalTau precision tau0348 contact0348 logTwoBall

theorem center_sq0348 : (center0348.re : ℝ)^2 +
    (center0348.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0348]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0348 : work0348.theta.ok = true ∧
    work0348.jac.invOK = true ∧ acceptsUnitSq work0348.out = true := by
  norm_num [work0348, contact0348, tau0348, center0348, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0348 : CellCertificate where
  tauBall := tau0348
  contactCenter := center0348
  contactBall := contact0348
  work := work0348
  center_sq := center_sq0348
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0348.1
  jac_ok := checks0348.2.1
  accepted := checks0348.2.2

def tau0349 : RatBall :=
  ⟨⟨-49/160, -33/160⟩, 3/320⟩
def center0349 : GaussianRat :=
  ⟨-8553183/40000000, -26276749/200000000⟩
def contact0349 : RatBall := localContactBall tau0349 center0349
def work0349 : RoundedTauEval :=
  evalTau precision tau0349 contact0349 logTwoBall

theorem center_sq0349 : (center0349.re : ℝ)^2 +
    (center0349.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0349]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0349 : work0349.theta.ok = true ∧
    work0349.jac.invOK = true ∧ acceptsUnitSq work0349.out = true := by
  norm_num [work0349, contact0349, tau0349, center0349, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0349 : CellCertificate where
  tauBall := tau0349
  contactCenter := center0349
  contactBall := contact0349
  work := work0349
  center_sq := center_sq0349
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0349.1
  jac_ok := checks0349.2.1
  accepted := checks0349.2.2

def tau0350 : RatBall :=
  ⟨⟨-43/160, -41/160⟩, 3/320⟩
def center0350 : GaussianRat :=
  ⟨-193470247/1000000000, -167770653/1000000000⟩
def contact0350 : RatBall := localContactBall tau0350 center0350
def work0350 : RoundedTauEval :=
  evalTau precision tau0350 contact0350 logTwoBall

theorem center_sq0350 : (center0350.re : ℝ)^2 +
    (center0350.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0350]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0350 : work0350.theta.ok = true ∧
    work0350.jac.invOK = true ∧ acceptsUnitSq work0350.out = true := by
  norm_num [work0350, contact0350, tau0350, center0350, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0350 : CellCertificate where
  tauBall := tau0350
  contactCenter := center0350
  contactBall := contact0350
  work := work0350
  center_sq := center_sq0350
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0350.1
  jac_ok := checks0350.2.1
  accepted := checks0350.2.2

def tau0351 : RatBall :=
  ⟨⟨-41/160, -41/160⟩, 3/320⟩
def center0351 : GaussianRat :=
  ⟨-184996961/1000000000, -21119029/125000000⟩
def contact0351 : RatBall := localContactBall tau0351 center0351
def work0351 : RoundedTauEval :=
  evalTau precision tau0351 contact0351 logTwoBall

theorem center_sq0351 : (center0351.re : ℝ)^2 +
    (center0351.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0351]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0351 : work0351.theta.ok = true ∧
    work0351.jac.invOK = true ∧ acceptsUnitSq work0351.out = true := by
  norm_num [work0351, contact0351, tau0351, center0351, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0351 : CellCertificate where
  tauBall := tau0351
  contactCenter := center0351
  contactBall := contact0351
  work := work0351
  center_sq := center_sq0351
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0351.1
  jac_ok := checks0351.2.1
  accepted := checks0351.2.2

def cells : List CellCertificate := [cell0344, cell0345, cell0346, cell0347, cell0348, cell0349, cell0350, cell0351]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043
