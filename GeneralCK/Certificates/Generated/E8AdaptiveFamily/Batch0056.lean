import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0448 : RatBall :=
  ⟨⟨-5/32, -41/160⟩, 3/320⟩
def center0448 : GaussianRat :=
  ⟨-114906151/1000000000, -176804909/1000000000⟩
def contact0448 : RatBall := localContactBall tau0448 center0448
def work0448 : RoundedTauEval :=
  evalTau precision tau0448 contact0448 logTwoBall

theorem center_sq0448 : (center0448.re : ℝ)^2 +
    (center0448.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0448]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0448 : work0448.theta.ok = true ∧
    work0448.jac.invOK = true ∧ acceptsUnitSq work0448.out = true := by
  norm_num [work0448, contact0448, tau0448, center0448, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0448 : CellCertificate where
  tauBall := tau0448
  contactCenter := center0448
  contactBall := contact0448
  work := work0448
  center_sq := center_sq0448
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0448.1
  jac_ok := checks0448.2.1
  accepted := checks0448.2.2

def tau0449 : RatBall :=
  ⟨⟨-23/160, -47/160⟩, 3/320⟩
def center0449 : GaussianRat :=
  ⟨-108280123/1000000000, -204924443/1000000000⟩
def contact0449 : RatBall := localContactBall tau0449 center0449
def work0449 : RoundedTauEval :=
  evalTau precision tau0449 contact0449 logTwoBall

theorem center_sq0449 : (center0449.re : ℝ)^2 +
    (center0449.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0449]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0449 : work0449.theta.ok = true ∧
    work0449.jac.invOK = true ∧ acceptsUnitSq work0449.out = true := by
  norm_num [work0449, contact0449, tau0449, center0449, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0449 : CellCertificate where
  tauBall := tau0449
  contactCenter := center0449
  contactBall := contact0449
  work := work0449
  center_sq := center_sq0449
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0449.1
  jac_ok := checks0449.2.1
  accepted := checks0449.2.2

def tau0450 : RatBall :=
  ⟨⟨-21/160, -47/160⟩, 3/320⟩
def center0450 : GaussianRat :=
  ⟨-618987/6250000, -102878573/500000000⟩
def contact0450 : RatBall := localContactBall tau0450 center0450
def work0450 : RoundedTauEval :=
  evalTau precision tau0450 contact0450 logTwoBall

theorem center_sq0450 : (center0450.re : ℝ)^2 +
    (center0450.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0450]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0450 : work0450.theta.ok = true ∧
    work0450.jac.invOK = true ∧ acceptsUnitSq work0450.out = true := by
  norm_num [work0450, contact0450, tau0450, center0450, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0450 : CellCertificate where
  tauBall := tau0450
  contactCenter := center0450
  contactBall := contact0450
  work := work0450
  center_sq := center_sq0450
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0450.1
  jac_ok := checks0450.2.1
  accepted := checks0450.2.2

def tau0451 : RatBall :=
  ⟨⟨-23/160, -9/32⟩, 3/320⟩
def center0451 : GaussianRat :=
  ⟨-107438161/1000000000, -195739697/1000000000⟩
def contact0451 : RatBall := localContactBall tau0451 center0451
def work0451 : RoundedTauEval :=
  evalTau precision tau0451 contact0451 logTwoBall

theorem center_sq0451 : (center0451.re : ℝ)^2 +
    (center0451.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0451]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0451 : work0451.theta.ok = true ∧
    work0451.jac.invOK = true ∧ acceptsUnitSq work0451.out = true := by
  norm_num [work0451, contact0451, tau0451, center0451, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0451 : CellCertificate where
  tauBall := tau0451
  contactCenter := center0451
  contactBall := contact0451
  work := work0451
  center_sq := center_sq0451
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0451.1
  jac_ok := checks0451.2.1
  accepted := checks0451.2.2

def tau0452 : RatBall :=
  ⟨⟨-21/160, -9/32⟩, 3/320⟩
def center0452 : GaussianRat :=
  ⟨-2456559/25000000, -19652513/100000000⟩
def contact0452 : RatBall := localContactBall tau0452 center0452
def work0452 : RoundedTauEval :=
  evalTau precision tau0452 contact0452 logTwoBall

theorem center_sq0452 : (center0452.re : ℝ)^2 +
    (center0452.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0452]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0452 : work0452.theta.ok = true ∧
    work0452.jac.invOK = true ∧ acceptsUnitSq work0452.out = true := by
  norm_num [work0452, contact0452, tau0452, center0452, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0452 : CellCertificate where
  tauBall := tau0452
  contactCenter := center0452
  contactBall := contact0452
  work := work0452
  center_sq := center_sq0452
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0452.1
  jac_ok := checks0452.2.1
  accepted := checks0452.2.2

def tau0453 : RatBall :=
  ⟨⟨-19/160, -47/160⟩, 3/320⟩
def center0453 : GaussianRat :=
  ⟨-89749431/1000000000, -206520639/1000000000⟩
def contact0453 : RatBall := localContactBall tau0453 center0453
def work0453 : RoundedTauEval :=
  evalTau precision tau0453 contact0453 logTwoBall

theorem center_sq0453 : (center0453.re : ℝ)^2 +
    (center0453.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0453]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0453 : work0453.theta.ok = true ∧
    work0453.jac.invOK = true ∧ acceptsUnitSq work0453.out = true := by
  norm_num [work0453, contact0453, tau0453, center0453, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0453 : CellCertificate where
  tauBall := tau0453
  contactCenter := center0453
  contactBall := contact0453
  work := work0453
  center_sq := center_sq0453
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0453.1
  jac_ok := checks0453.2.1
  accepted := checks0453.2.2

def tau0454 : RatBall :=
  ⟨⟨-17/160, -47/160⟩, 3/320⟩
def center0454 : GaussianRat :=
  ⟨-20104647/250000000, -10360657/50000000⟩
def contact0454 : RatBall := localContactBall tau0454 center0454
def work0454 : RoundedTauEval :=
  evalTau precision tau0454 contact0454 logTwoBall

theorem center_sq0454 : (center0454.re : ℝ)^2 +
    (center0454.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0454]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0454 : work0454.theta.ok = true ∧
    work0454.jac.invOK = true ∧ acceptsUnitSq work0454.out = true := by
  norm_num [work0454, contact0454, tau0454, center0454, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0454 : CellCertificate where
  tauBall := tau0454
  contactCenter := center0454
  contactBall := contact0454
  work := work0454
  center_sq := center_sq0454
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0454.1
  jac_ok := checks0454.2.1
  accepted := checks0454.2.2

def tau0455 : RatBall :=
  ⟨⟨-19/160, -9/32⟩, 3/320⟩
def center0455 : GaussianRat :=
  ⟨-22260513/250000000, -49311287/250000000⟩
def contact0455 : RatBall := localContactBall tau0455 center0455
def work0455 : RoundedTauEval :=
  evalTau precision tau0455 contact0455 logTwoBall

theorem center_sq0455 : (center0455.re : ℝ)^2 +
    (center0455.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0455]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0455 : work0455.theta.ok = true ∧
    work0455.jac.invOK = true ∧ acceptsUnitSq work0455.out = true := by
  norm_num [work0455, contact0455, tau0455, center0455, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0455 : CellCertificate where
  tauBall := tau0455
  contactCenter := center0455
  contactBall := contact0455
  work := work0455
  center_sq := center_sq0455
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0455.1
  jac_ok := checks0455.2.1
  accepted := checks0455.2.2

def cells : List CellCertificate := [cell0448, cell0449, cell0450, cell0451, cell0452, cell0453, cell0454, cell0455]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056
