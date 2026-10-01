import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0176

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1408 : RatBall :=
  ⟨⟨-59/320, -99/320⟩, 3/640⟩
def center1408 : GaussianRat :=
  ⟨-34836127/250000000, -53276923/250000000⟩
def contact1408 : RatBall := localContactBall tau1408 center1408
def work1408 : RoundedTauEval :=
  evalTau precision tau1408 contact1408 logTwoBall

theorem center_sq1408 : (center1408.re : ℝ)^2 +
    (center1408.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1408]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1408 : work1408.theta.ok = true ∧
    work1408.jac.invOK = true ∧ acceptsUnitSq work1408.out = true := by
  norm_num [work1408, contact1408, tau1408, center1408, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1408 : CellCertificate where
  tauBall := tau1408
  contactCenter := center1408
  contactBall := contact1408
  work := work1408
  center_sq := center_sq1408
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1408.1
  jac_ok := checks1408.2.1
  accepted := checks1408.2.2

def tau1409 : RatBall :=
  ⟨⟨-57/320, -99/320⟩, 3/640⟩
def center1409 : GaussianRat :=
  ⟨-5391177/40000000, -106838001/500000000⟩
def contact1409 : RatBall := localContactBall tau1409 center1409
def work1409 : RoundedTauEval :=
  evalTau precision tau1409 contact1409 logTwoBall

theorem center_sq1409 : (center1409.re : ℝ)^2 +
    (center1409.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1409]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1409 : work1409.theta.ok = true ∧
    work1409.jac.invOK = true ∧ acceptsUnitSq work1409.out = true := by
  norm_num [work1409, contact1409, tau1409, center1409, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1409 : CellCertificate where
  tauBall := tau1409
  contactCenter := center1409
  contactBall := contact1409
  work := work1409
  center_sq := center_sq1409
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1409.1
  jac_ok := checks1409.2.1
  accepted := checks1409.2.2

def tau1410 : RatBall :=
  ⟨⟨-59/320, -97/320⟩, 3/640⟩
def center1410 : GaussianRat :=
  ⟨-13877609/100000000, -208558553/1000000000⟩
def contact1410 : RatBall := localContactBall tau1410 center1410
def work1410 : RoundedTauEval :=
  evalTau precision tau1410 contact1410 logTwoBall

theorem center_sq1410 : (center1410.re : ℝ)^2 +
    (center1410.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1410]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1410 : work1410.theta.ok = true ∧
    work1410.jac.invOK = true ∧ acceptsUnitSq work1410.out = true := by
  norm_num [work1410, contact1410, tau1410, center1410, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1410 : CellCertificate where
  tauBall := tau1410
  contactCenter := center1410
  contactBall := contact1410
  work := work1410
  center_sq := center_sq1410
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1410.1
  jac_ok := checks1410.2.1
  accepted := checks1410.2.2

def tau1411 : RatBall :=
  ⟨⟨-57/320, -97/320⟩, 3/640⟩
def center1411 : GaussianRat :=
  ⟨-67113521/500000000, -52277787/250000000⟩
def contact1411 : RatBall := localContactBall tau1411 center1411
def work1411 : RoundedTauEval :=
  evalTau precision tau1411 contact1411 logTwoBall

theorem center_sq1411 : (center1411.re : ℝ)^2 +
    (center1411.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1411]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1411 : work1411.theta.ok = true ∧
    work1411.jac.invOK = true ∧ acceptsUnitSq work1411.out = true := by
  norm_num [work1411, contact1411, tau1411, center1411, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1411 : CellCertificate where
  tauBall := tau1411
  contactCenter := center1411
  contactBall := contact1411
  work := work1411
  center_sq := center_sq1411
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1411.1
  jac_ok := checks1411.2.1
  accepted := checks1411.2.2

def tau1412 : RatBall :=
  ⟨⟨-11/64, -103/320⟩, 3/640⟩
def center1412 : GaussianRat :=
  ⟨-8207299/62500000, -8937551/40000000⟩
def contact1412 : RatBall := localContactBall tau1412 center1412
def work1412 : RoundedTauEval :=
  evalTau precision tau1412 contact1412 logTwoBall

theorem center_sq1412 : (center1412.re : ℝ)^2 +
    (center1412.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1412]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1412 : work1412.theta.ok = true ∧
    work1412.jac.invOK = true ∧ acceptsUnitSq work1412.out = true := by
  norm_num [work1412, contact1412, tau1412, center1412, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1412 : CellCertificate where
  tauBall := tau1412
  contactCenter := center1412
  contactBall := contact1412
  work := work1412
  center_sq := center_sq1412
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1412.1
  jac_ok := checks1412.2.1
  accepted := checks1412.2.2

def tau1413 : RatBall :=
  ⟨⟨-53/320, -103/320⟩, 3/640⟩
def center1413 : GaussianRat :=
  ⟨-126686203/1000000000, -224004631/1000000000⟩
def contact1413 : RatBall := localContactBall tau1413 center1413
def work1413 : RoundedTauEval :=
  evalTau precision tau1413 contact1413 logTwoBall

theorem center_sq1413 : (center1413.re : ℝ)^2 +
    (center1413.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1413]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1413 : work1413.theta.ok = true ∧
    work1413.jac.invOK = true ∧ acceptsUnitSq work1413.out = true := by
  norm_num [work1413, contact1413, tau1413, center1413, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1413 : CellCertificate where
  tauBall := tau1413
  contactCenter := center1413
  contactBall := contact1413
  work := work1413
  center_sq := center_sq1413
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1413.1
  jac_ok := checks1413.2.1
  accepted := checks1413.2.2

def tau1414 : RatBall :=
  ⟨⟨-11/64, -101/320⟩, 3/640⟩
def center1414 : GaussianRat :=
  ⟨-3268749/25000000, -54706193/250000000⟩
def contact1414 : RatBall := localContactBall tau1414 center1414
def work1414 : RoundedTauEval :=
  evalTau precision tau1414 contact1414 logTwoBall

theorem center_sq1414 : (center1414.re : ℝ)^2 +
    (center1414.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1414]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1414 : work1414.theta.ok = true ∧
    work1414.jac.invOK = true ∧ acceptsUnitSq work1414.out = true := by
  norm_num [work1414, contact1414, tau1414, center1414, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1414 : CellCertificate where
  tauBall := tau1414
  contactCenter := center1414
  contactBall := contact1414
  work := work1414
  center_sq := center_sq1414
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1414.1
  jac_ok := checks1414.2.1
  accepted := checks1414.2.2

def tau1415 : RatBall :=
  ⟨⟨-53/320, -101/320⟩, 3/640⟩
def center1415 : GaussianRat :=
  ⟨-15767113/125000000, -219375147/1000000000⟩
def contact1415 : RatBall := localContactBall tau1415 center1415
def work1415 : RoundedTauEval :=
  evalTau precision tau1415 contact1415 logTwoBall

theorem center_sq1415 : (center1415.re : ℝ)^2 +
    (center1415.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1415]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1415 : work1415.theta.ok = true ∧
    work1415.jac.invOK = true ∧ acceptsUnitSq work1415.out = true := by
  norm_num [work1415, contact1415, tau1415, center1415, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1415 : CellCertificate where
  tauBall := tau1415
  contactCenter := center1415
  contactBall := contact1415
  work := work1415
  center_sq := center_sq1415
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1415.1
  jac_ok := checks1415.2.1
  accepted := checks1415.2.2

def cells : List CellCertificate := [cell1408, cell1409, cell1410, cell1411, cell1412, cell1413, cell1414, cell1415]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0176
