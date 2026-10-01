import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0179

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1432 : RatBall :=
  ⟨⟨-43/320, -107/320⟩, 3/640⟩
def center1432 : GaussianRat :=
  ⟨-104264923/1000000000, -236017459/1000000000⟩
def contact1432 : RatBall := localContactBall tau1432 center1432
def work1432 : RoundedTauEval :=
  evalTau precision tau1432 contact1432 logTwoBall

theorem center_sq1432 : (center1432.re : ℝ)^2 +
    (center1432.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1432]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1432 : work1432.theta.ok = true ∧
    work1432.jac.invOK = true ∧ acceptsUnitSq work1432.out = true := by
  norm_num [work1432, contact1432, tau1432, center1432, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1432 : CellCertificate where
  tauBall := tau1432
  contactCenter := center1432
  contactBall := contact1432
  work := work1432
  center_sq := center_sq1432
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1432.1
  jac_ok := checks1432.2.1
  accepted := checks1432.2.2

def tau1433 : RatBall :=
  ⟨⟨-41/320, -107/320⟩, 3/640⟩
def center1433 : GaussianRat :=
  ⟨-99508871/1000000000, -236497219/1000000000⟩
def contact1433 : RatBall := localContactBall tau1433 center1433
def work1433 : RoundedTauEval :=
  evalTau precision tau1433 contact1433 logTwoBall

theorem center_sq1433 : (center1433.re : ℝ)^2 +
    (center1433.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1433]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1433 : work1433.theta.ok = true ∧
    work1433.jac.invOK = true ∧ acceptsUnitSq work1433.out = true := by
  norm_num [work1433, contact1433, tau1433, center1433, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1433 : CellCertificate where
  tauBall := tau1433
  contactCenter := center1433
  contactBall := contact1433
  work := work1433
  center_sq := center_sq1433
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1433.1
  jac_ok := checks1433.2.1
  accepted := checks1433.2.2

def tau1434 : RatBall :=
  ⟨⟨-43/320, -21/64⟩, 3/640⟩
def center1434 : GaussianRat :=
  ⟨-103781603/1000000000, -28909781/125000000⟩
def contact1434 : RatBall := localContactBall tau1434 center1434
def work1434 : RoundedTauEval :=
  evalTau precision tau1434 contact1434 logTwoBall

theorem center_sq1434 : (center1434.re : ℝ)^2 +
    (center1434.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1434]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1434 : work1434.theta.ok = true ∧
    work1434.jac.invOK = true ∧ acceptsUnitSq work1434.out = true := by
  norm_num [work1434, contact1434, tau1434, center1434, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1434 : CellCertificate where
  tauBall := tau1434
  contactCenter := center1434
  contactBall := contact1434
  work := work1434
  center_sq := center_sq1434
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1434.1
  jac_ok := checks1434.2.1
  accepted := checks1434.2.2

def tau1435 : RatBall :=
  ⟨⟨-41/320, -21/64⟩, 3/640⟩
def center1435 : GaussianRat :=
  ⟨-12380739/125000000, -115872433/500000000⟩
def contact1435 : RatBall := localContactBall tau1435 center1435
def work1435 : RoundedTauEval :=
  evalTau precision tau1435 contact1435 logTwoBall

theorem center_sq1435 : (center1435.re : ℝ)^2 +
    (center1435.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1435]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1435 : work1435.theta.ok = true ∧
    work1435.jac.invOK = true ∧ acceptsUnitSq work1435.out = true := by
  norm_num [work1435, contact1435, tau1435, center1435, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1435 : CellCertificate where
  tauBall := tau1435
  contactCenter := center1435
  contactBall := contact1435
  work := work1435
  center_sq := center_sq1435
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1435.1
  jac_ok := checks1435.2.1
  accepted := checks1435.2.2

def tau1436 : RatBall :=
  ⟨⟨-39/320, -111/320⟩, 3/640⟩
def center1436 : GaussianRat :=
  ⟨-11957763/125000000, -15409367/62500000⟩
def contact1436 : RatBall := localContactBall tau1436 center1436
def work1436 : RoundedTauEval :=
  evalTau precision tau1436 contact1436 logTwoBall

theorem center_sq1436 : (center1436.re : ℝ)^2 +
    (center1436.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1436]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1436 : work1436.theta.ok = true ∧
    work1436.jac.invOK = true ∧ acceptsUnitSq work1436.out = true := by
  norm_num [work1436, contact1436, tau1436, center1436, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1436 : CellCertificate where
  tauBall := tau1436
  contactCenter := center1436
  contactBall := contact1436
  work := work1436
  center_sq := center_sq1436
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1436.1
  jac_ok := checks1436.2.1
  accepted := checks1436.2.2

def tau1437 : RatBall :=
  ⟨⟨-37/320, -111/320⟩, 3/640⟩
def center1437 : GaussianRat :=
  ⟨-45418507/500000000, -247012717/1000000000⟩
def contact1437 : RatBall := localContactBall tau1437 center1437
def work1437 : RoundedTauEval :=
  evalTau precision tau1437 contact1437 logTwoBall

theorem center_sq1437 : (center1437.re : ℝ)^2 +
    (center1437.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1437]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1437 : work1437.theta.ok = true ∧
    work1437.jac.invOK = true ∧ acceptsUnitSq work1437.out = true := by
  norm_num [work1437, contact1437, tau1437, center1437, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1437 : CellCertificate where
  tauBall := tau1437
  contactCenter := center1437
  contactBall := contact1437
  work := work1437
  center_sq := center_sq1437
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1437.1
  jac_ok := checks1437.2.1
  accepted := checks1437.2.2

def tau1438 : RatBall :=
  ⟨⟨-39/320, -109/320⟩, 3/640⟩
def center1438 : GaussianRat :=
  ⟨-47597289/500000000, -241742219/1000000000⟩
def contact1438 : RatBall := localContactBall tau1438 center1438
def work1438 : RoundedTauEval :=
  evalTau precision tau1438 contact1438 logTwoBall

theorem center_sq1438 : (center1438.re : ℝ)^2 +
    (center1438.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1438]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1438 : work1438.theta.ok = true ∧
    work1438.jac.invOK = true ∧ acceptsUnitSq work1438.out = true := by
  norm_num [work1438, contact1438, tau1438, center1438, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1438 : CellCertificate where
  tauBall := tau1438
  contactCenter := center1438
  contactBall := contact1438
  work := work1438
  center_sq := center_sq1438
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1438.1
  jac_ok := checks1438.2.1
  accepted := checks1438.2.2

def tau1439 : RatBall :=
  ⟨⟨-37/320, -109/320⟩, 3/640⟩
def center1439 : GaussianRat :=
  ⟨-45195779/500000000, -121096227/500000000⟩
def contact1439 : RatBall := localContactBall tau1439 center1439
def work1439 : RoundedTauEval :=
  evalTau precision tau1439 contact1439 logTwoBall

theorem center_sq1439 : (center1439.re : ℝ)^2 +
    (center1439.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1439]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1439 : work1439.theta.ok = true ∧
    work1439.jac.invOK = true ∧ acceptsUnitSq work1439.out = true := by
  norm_num [work1439, contact1439, tau1439, center1439, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1439 : CellCertificate where
  tauBall := tau1439
  contactCenter := center1439
  contactBall := contact1439
  work := work1439
  center_sq := center_sq1439
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1439.1
  jac_ok := checks1439.2.1
  accepted := checks1439.2.2

def cells : List CellCertificate := [cell1432, cell1433, cell1434, cell1435, cell1436, cell1437, cell1438, cell1439]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0179
