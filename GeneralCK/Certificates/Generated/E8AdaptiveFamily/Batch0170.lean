import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1360 : RatBall :=
  ⟨⟨-39/320, -113/320⟩, 3/640⟩
def center1360 : GaussianRat :=
  ⟨-48071341/500000000, -251379737/1000000000⟩
def contact1360 : RatBall := localContactBall tau1360 center1360
def work1360 : RoundedTauEval :=
  evalTau precision tau1360 contact1360 logTwoBall

theorem center_sq1360 : (center1360.re : ℝ)^2 +
    (center1360.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1360]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1360 : work1360.theta.ok = true ∧
    work1360.jac.invOK = true ∧ acceptsUnitSq work1360.out = true := by
  norm_num [work1360, contact1360, tau1360, center1360, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1360 : CellCertificate where
  tauBall := tau1360
  contactCenter := center1360
  contactBall := contact1360
  work := work1360
  center_sq := center_sq1360
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1360.1
  jac_ok := checks1360.2.1
  accepted := checks1360.2.2

def tau1361 : RatBall :=
  ⟨⟨-37/320, -113/320⟩, 3/640⟩
def center1361 : GaussianRat :=
  ⟨-45647467/500000000, -62963873/250000000⟩
def contact1361 : RatBall := localContactBall tau1361 center1361
def work1361 : RoundedTauEval :=
  evalTau precision tau1361 contact1361 logTwoBall

theorem center_sq1361 : (center1361.re : ℝ)^2 +
    (center1361.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1361]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1361 : work1361.theta.ok = true ∧
    work1361.jac.invOK = true ∧ acceptsUnitSq work1361.out = true := by
  norm_num [work1361, contact1361, tau1361, center1361, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1361 : CellCertificate where
  tauBall := tau1361
  contactCenter := center1361
  contactBall := contact1361
  work := work1361
  center_sq := center_sq1361
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1361.1
  jac_ok := checks1361.2.1
  accepted := checks1361.2.2

def tau1362 : RatBall :=
  ⟨⟨-7/64, -23/64⟩, 3/640⟩
def center1362 : GaussianRat :=
  ⟨-43440767/500000000, -257186633/1000000000⟩
def contact1362 : RatBall := localContactBall tau1362 center1362
def work1362 : RoundedTauEval :=
  evalTau precision tau1362 contact1362 logTwoBall

theorem center_sq1362 : (center1362.re : ℝ)^2 +
    (center1362.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1362]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1362 : work1362.theta.ok = true ∧
    work1362.jac.invOK = true ∧ acceptsUnitSq work1362.out = true := by
  norm_num [work1362, contact1362, tau1362, center1362, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1362 : CellCertificate where
  tauBall := tau1362
  contactCenter := center1362
  contactBall := contact1362
  work := work1362
  center_sq := center_sq1362
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1362.1
  jac_ok := checks1362.2.1
  accepted := checks1362.2.2

def tau1363 : RatBall :=
  ⟨⟨-33/320, -23/64⟩, 3/640⟩
def center1363 : GaussianRat :=
  ⟨-40992501/500000000, -257627847/1000000000⟩
def contact1363 : RatBall := localContactBall tau1363 center1363
def work1363 : RoundedTauEval :=
  evalTau precision tau1363 contact1363 logTwoBall

theorem center_sq1363 : (center1363.re : ℝ)^2 +
    (center1363.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1363]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1363 : work1363.theta.ok = true ∧
    work1363.jac.invOK = true ∧ acceptsUnitSq work1363.out = true := by
  norm_num [work1363, contact1363, tau1363, center1363, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1363 : CellCertificate where
  tauBall := tau1363
  contactCenter := center1363
  contactBall := contact1363
  work := work1363
  center_sq := center_sq1363
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1363.1
  jac_ok := checks1363.2.1
  accepted := checks1363.2.2

def tau1364 : RatBall :=
  ⟨⟨-7/64, -113/320⟩, 3/640⟩
def center1364 : GaussianRat :=
  ⟨-86434423/1000000000, -50461627/200000000⟩
def contact1364 : RatBall := localContactBall tau1364 center1364
def work1364 : RoundedTauEval :=
  evalTau precision tau1364 contact1364 logTwoBall

theorem center_sq1364 : (center1364.re : ℝ)^2 +
    (center1364.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1364]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1364 : work1364.theta.ok = true ∧
    work1364.jac.invOK = true ∧ acceptsUnitSq work1364.out = true := by
  norm_num [work1364, contact1364, tau1364, center1364, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1364 : CellCertificate where
  tauBall := tau1364
  contactCenter := center1364
  contactBall := contact1364
  work := work1364
  center_sq := center_sq1364
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1364.1
  jac_ok := checks1364.2.1
  accepted := checks1364.2.2

def tau1365 : RatBall :=
  ⟨⟨-33/320, -113/320⟩, 3/640⟩
def center1365 : GaussianRat :=
  ⟨-16312353/200000000, -252737367/1000000000⟩
def contact1365 : RatBall := localContactBall tau1365 center1365
def work1365 : RoundedTauEval :=
  evalTau precision tau1365 contact1365 logTwoBall

theorem center_sq1365 : (center1365.re : ℝ)^2 +
    (center1365.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1365]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1365 : work1365.theta.ok = true ∧
    work1365.jac.invOK = true ∧ acceptsUnitSq work1365.out = true := by
  norm_num [work1365, contact1365, tau1365, center1365, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1365 : CellCertificate where
  tauBall := tau1365
  contactCenter := center1365
  contactBall := contact1365
  work := work1365
  center_sq := center_sq1365
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1365.1
  jac_ok := checks1365.2.1
  accepted := checks1365.2.2

def tau1366 : RatBall :=
  ⟨⟨-63/320, -109/320⟩, 3/640⟩
def center1366 : GaussianRat :=
  ⟨-75841877/500000000, -234745077/1000000000⟩
def contact1366 : RatBall := localContactBall tau1366 center1366
def work1366 : RoundedTauEval :=
  evalTau precision tau1366 contact1366 logTwoBall

theorem center_sq1366 : (center1366.re : ℝ)^2 +
    (center1366.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1366]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1366 : work1366.theta.ok = true ∧
    work1366.jac.invOK = true ∧ acceptsUnitSq work1366.out = true := by
  norm_num [work1366, contact1366, tau1366, center1366, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1366 : CellCertificate where
  tauBall := tau1366
  contactCenter := center1366
  contactBall := contact1366
  work := work1366
  center_sq := center_sq1366
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1366.1
  jac_ok := checks1366.2.1
  accepted := checks1366.2.2

def tau1367 : RatBall :=
  ⟨⟨-61/320, -109/320⟩, 3/640⟩
def center1367 : GaussianRat :=
  ⟨-147068213/1000000000, -14714559/62500000⟩
def contact1367 : RatBall := localContactBall tau1367 center1367
def work1367 : RoundedTauEval :=
  evalTau precision tau1367 contact1367 logTwoBall

theorem center_sq1367 : (center1367.re : ℝ)^2 +
    (center1367.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1367]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1367 : work1367.theta.ok = true ∧
    work1367.jac.invOK = true ∧ acceptsUnitSq work1367.out = true := by
  norm_num [work1367, contact1367, tau1367, center1367, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1367 : CellCertificate where
  tauBall := tau1367
  contactCenter := center1367
  contactBall := contact1367
  work := work1367
  center_sq := center_sq1367
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1367.1
  jac_ok := checks1367.2.1
  accepted := checks1367.2.2

def cells : List CellCertificate := [cell1360, cell1361, cell1362, cell1363, cell1364, cell1365, cell1366, cell1367]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170
