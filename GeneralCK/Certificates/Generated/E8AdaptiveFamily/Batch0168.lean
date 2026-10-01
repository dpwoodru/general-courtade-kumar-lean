import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1344 : RatBall :=
  ⟨⟨-53/320, -113/320⟩, 3/640⟩
def center1344 : GaussianRat :=
  ⟨-129670733/1000000000, -15464381/62500000⟩
def contact1344 : RatBall := localContactBall tau1344 center1344
def work1344 : RoundedTauEval :=
  evalTau precision tau1344 contact1344 logTwoBall

theorem center_sq1344 : (center1344.re : ℝ)^2 +
    (center1344.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1344]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1344 : work1344.theta.ok = true ∧
    work1344.jac.invOK = true ∧ acceptsUnitSq work1344.out = true := by
  norm_num [work1344, contact1344, tau1344, center1344, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1344 : CellCertificate where
  tauBall := tau1344
  contactCenter := center1344
  contactBall := contact1344
  work := work1344
  center_sq := center_sq1344
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1344.1
  jac_ok := checks1344.2.1
  accepted := checks1344.2.2

def tau1345 : RatBall :=
  ⟨⟨-51/320, -113/320⟩, 3/640⟩
def center1345 : GaussianRat :=
  ⟨-124928411/1000000000, -12402911/50000000⟩
def contact1345 : RatBall := localContactBall tau1345 center1345
def work1345 : RoundedTauEval :=
  evalTau precision tau1345 contact1345 logTwoBall

theorem center_sq1345 : (center1345.re : ℝ)^2 +
    (center1345.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1345]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1345 : work1345.theta.ok = true ∧
    work1345.jac.invOK = true ∧ acceptsUnitSq work1345.out = true := by
  norm_num [work1345, contact1345, tau1345, center1345, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1345 : CellCertificate where
  tauBall := tau1345
  contactCenter := center1345
  contactBall := contact1345
  work := work1345
  center_sq := center_sq1345
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1345.1
  jac_ok := checks1345.2.1
  accepted := checks1345.2.2

def tau1346 : RatBall :=
  ⟨⟨-49/320, -113/320⟩, 3/640⟩
def center1346 : GaussianRat :=
  ⟨-120169401/1000000000, -248665661/1000000000⟩
def contact1346 : RatBall := localContactBall tau1346 center1346
def work1346 : RoundedTauEval :=
  evalTau precision tau1346 contact1346 logTwoBall

theorem center_sq1346 : (center1346.re : ℝ)^2 +
    (center1346.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1346]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1346 : work1346.theta.ok = true ∧
    work1346.jac.invOK = true ∧ acceptsUnitSq work1346.out = true := by
  norm_num [work1346, contact1346, tau1346, center1346, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1346 : CellCertificate where
  tauBall := tau1346
  contactCenter := center1346
  contactBall := contact1346
  work := work1346
  center_sq := center_sq1346
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1346.1
  jac_ok := checks1346.2.1
  accepted := checks1346.2.2

def tau1347 : RatBall :=
  ⟨⟨-9/64, -23/64⟩, 3/640⟩
def center1347 : GaussianRat :=
  ⟨-889321/8000000, -254626433/1000000000⟩
def contact1347 : RatBall := localContactBall tau1347 center1347
def work1347 : RoundedTauEval :=
  evalTau precision tau1347 contact1347 logTwoBall

theorem center_sq1347 : (center1347.re : ℝ)^2 +
    (center1347.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1347 : work1347.theta.ok = true ∧
    work1347.jac.invOK = true ∧ acceptsUnitSq work1347.out = true := by
  norm_num [work1347, contact1347, tau1347, center1347, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1347 : CellCertificate where
  tauBall := tau1347
  contactCenter := center1347
  contactBall := contact1347
  work := work1347
  center_sq := center_sq1347
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1347.1
  jac_ok := checks1347.2.1
  accepted := checks1347.2.2

def tau1348 : RatBall :=
  ⟨⟨-47/320, -113/320⟩, 3/640⟩
def center1348 : GaussianRat :=
  ⟨-115394221/1000000000, -124626021/500000000⟩
def contact1348 : RatBall := localContactBall tau1348 center1348
def work1348 : RoundedTauEval :=
  evalTau precision tau1348 contact1348 logTwoBall

theorem center_sq1348 : (center1348.re : ℝ)^2 +
    (center1348.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1348]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1348 : work1348.theta.ok = true ∧
    work1348.jac.invOK = true ∧ acceptsUnitSq work1348.out = true := by
  norm_num [work1348, contact1348, tau1348, center1348, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1348 : CellCertificate where
  tauBall := tau1348
  contactCenter := center1348
  contactBall := contact1348
  work := work1348
  center_sq := center_sq1348
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1348.1
  jac_ok := checks1348.2.1
  accepted := checks1348.2.2

def tau1349 : RatBall :=
  ⟨⟨-9/64, -113/320⟩, 3/640⟩
def center1349 : GaussianRat :=
  ⟨-22120681/200000000, -249816993/1000000000⟩
def contact1349 : RatBall := localContactBall tau1349 center1349
def work1349 : RoundedTauEval :=
  evalTau precision tau1349 contact1349 logTwoBall

theorem center_sq1349 : (center1349.re : ℝ)^2 +
    (center1349.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1349]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1349 : work1349.theta.ok = true ∧
    work1349.jac.invOK = true ∧ acceptsUnitSq work1349.out = true := by
  norm_num [work1349, contact1349, tau1349, center1349, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1349 : CellCertificate where
  tauBall := tau1349
  contactCenter := center1349
  contactBall := contact1349
  work := work1349
  center_sq := center_sq1349
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1349.1
  jac_ok := checks1349.2.1
  accepted := checks1349.2.2

def tau1350 : RatBall :=
  ⟨⟨-43/320, -23/64⟩, 3/640⟩
def center1350 : GaussianRat :=
  ⟨-106336973/1000000000, -255184583/1000000000⟩
def contact1350 : RatBall := localContactBall tau1350 center1350
def work1350 : RoundedTauEval :=
  evalTau precision tau1350 contact1350 logTwoBall

theorem center_sq1350 : (center1350.re : ℝ)^2 +
    (center1350.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1350]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1350 : work1350.theta.ok = true ∧
    work1350.jac.invOK = true ∧ acceptsUnitSq work1350.out = true := by
  norm_num [work1350, contact1350, tau1350, center1350, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1350 : CellCertificate where
  tauBall := tau1350
  contactCenter := center1350
  contactBall := contact1350
  work := work1350
  center_sq := center_sq1350
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1350.1
  jac_ok := checks1350.2.1
  accepted := checks1350.2.2

def tau1351 : RatBall :=
  ⟨⟨-41/320, -23/64⟩, 3/640⟩
def center1351 : GaussianRat :=
  ⟨-12686743/125000000, -255720023/1000000000⟩
def contact1351 : RatBall := localContactBall tau1351 center1351
def work1351 : RoundedTauEval :=
  evalTau precision tau1351 contact1351 logTwoBall

theorem center_sq1351 : (center1351.re : ℝ)^2 +
    (center1351.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1351]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1351 : work1351.theta.ok = true ∧
    work1351.jac.invOK = true ∧ acceptsUnitSq work1351.out = true := by
  norm_num [work1351, contact1351, tau1351, center1351, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1351 : CellCertificate where
  tauBall := tau1351
  contactCenter := center1351
  contactBall := contact1351
  work := work1351
  center_sq := center_sq1351
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1351.1
  jac_ok := checks1351.2.1
  accepted := checks1351.2.2

def cells : List CellCertificate := [cell1344, cell1345, cell1346, cell1347, cell1348, cell1349, cell1350, cell1351]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168
