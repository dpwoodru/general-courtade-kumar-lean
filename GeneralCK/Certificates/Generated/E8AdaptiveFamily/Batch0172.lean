import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1376 : RatBall :=
  ⟨⟨-59/320, -107/320⟩, 3/640⟩
def center1376 : GaussianRat :=
  ⟨-141782257/1000000000, -231469249/1000000000⟩
def contact1376 : RatBall := localContactBall tau1376 center1376
def work1376 : RoundedTauEval :=
  evalTau precision tau1376 contact1376 logTwoBall

theorem center_sq1376 : (center1376.re : ℝ)^2 +
    (center1376.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1376]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1376 : work1376.theta.ok = true ∧
    work1376.jac.invOK = true ∧ acceptsUnitSq work1376.out = true := by
  norm_num [work1376, contact1376, tau1376, center1376, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1376 : CellCertificate where
  tauBall := tau1376
  contactCenter := center1376
  contactBall := contact1376
  work := work1376
  center_sq := center_sq1376
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1376.1
  jac_ok := checks1376.2.1
  accepted := checks1376.2.2

def tau1377 : RatBall :=
  ⟨⟨-57/320, -107/320⟩, 3/640⟩
def center1377 : GaussianRat :=
  ⟨-6857441/50000000, -46420737/200000000⟩
def contact1377 : RatBall := localContactBall tau1377 center1377
def work1377 : RoundedTauEval :=
  evalTau precision tau1377 contact1377 logTwoBall

theorem center_sq1377 : (center1377.re : ℝ)^2 +
    (center1377.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1377]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1377 : work1377.theta.ok = true ∧
    work1377.jac.invOK = true ∧ acceptsUnitSq work1377.out = true := by
  norm_num [work1377, contact1377, tau1377, center1377, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1377 : CellCertificate where
  tauBall := tau1377
  contactCenter := center1377
  contactBall := contact1377
  work := work1377
  center_sq := center_sq1377
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1377.1
  jac_ok := checks1377.2.1
  accepted := checks1377.2.2

def tau1378 : RatBall :=
  ⟨⟨-59/320, -21/64⟩, 3/640⟩
def center1378 : GaussianRat :=
  ⟨-70573769/500000000, -113426637/500000000⟩
def contact1378 : RatBall := localContactBall tau1378 center1378
def work1378 : RoundedTauEval :=
  evalTau precision tau1378 contact1378 logTwoBall

theorem center_sq1378 : (center1378.re : ℝ)^2 +
    (center1378.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1378]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1378 : work1378.theta.ok = true ∧
    work1378.jac.invOK = true ∧ acceptsUnitSq work1378.out = true := by
  norm_num [work1378, contact1378, tau1378, center1378, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1378 : CellCertificate where
  tauBall := tau1378
  contactCenter := center1378
  contactBall := contact1378
  work := work1378
  center_sq := center_sq1378
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1378.1
  jac_ok := checks1378.2.1
  accepted := checks1378.2.2

def tau1379 : RatBall :=
  ⟨⟨-57/320, -21/64⟩, 3/640⟩
def center1379 : GaussianRat :=
  ⟨-136531833/1000000000, -227470663/1000000000⟩
def contact1379 : RatBall := localContactBall tau1379 center1379
def work1379 : RoundedTauEval :=
  evalTau precision tau1379 contact1379 logTwoBall

theorem center_sq1379 : (center1379.re : ℝ)^2 +
    (center1379.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1379]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1379 : work1379.theta.ok = true ∧
    work1379.jac.invOK = true ∧ acceptsUnitSq work1379.out = true := by
  norm_num [work1379, contact1379, tau1379, center1379, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1379 : CellCertificate where
  tauBall := tau1379
  contactCenter := center1379
  contactBall := contact1379
  work := work1379
  center_sq := center_sq1379
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1379.1
  jac_ok := checks1379.2.1
  accepted := checks1379.2.2

def tau1380 : RatBall :=
  ⟨⟨-11/64, -111/320⟩, 3/640⟩
def center1380 : GaussianRat :=
  ⟨-133746201/1000000000, -121037589/500000000⟩
def contact1380 : RatBall := localContactBall tau1380 center1380
def work1380 : RoundedTauEval :=
  evalTau precision tau1380 contact1380 logTwoBall

theorem center_sq1380 : (center1380.re : ℝ)^2 +
    (center1380.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1380]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1380 : work1380.theta.ok = true ∧
    work1380.jac.invOK = true ∧ acceptsUnitSq work1380.out = true := by
  norm_num [work1380, contact1380, tau1380, center1380, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1380 : CellCertificate where
  tauBall := tau1380
  contactCenter := center1380
  contactBall := contact1380
  work := work1380
  center_sq := center_sq1380
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1380.1
  jac_ok := checks1380.2.1
  accepted := checks1380.2.2

def tau1381 : RatBall :=
  ⟨⟨-53/320, -111/320⟩, 3/640⟩
def center1381 : GaussianRat :=
  ⟨-4032529/31250000, -121353177/500000000⟩
def contact1381 : RatBall := localContactBall tau1381 center1381
def work1381 : RoundedTauEval :=
  evalTau precision tau1381 contact1381 logTwoBall

theorem center_sq1381 : (center1381.re : ℝ)^2 +
    (center1381.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1381]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1381 : work1381.theta.ok = true ∧
    work1381.jac.invOK = true ∧ acceptsUnitSq work1381.out = true := by
  norm_num [work1381, contact1381, tau1381, center1381, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1381 : CellCertificate where
  tauBall := tau1381
  contactCenter := center1381
  contactBall := contact1381
  work := work1381
  center_sq := center_sq1381
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1381.1
  jac_ok := checks1381.2.1
  accepted := checks1381.2.2

def tau1382 : RatBall :=
  ⟨⟨-11/64, -109/320⟩, 3/640⟩
def center1382 : GaussianRat :=
  ⟨-133113831/1000000000, -118694053/500000000⟩
def contact1382 : RatBall := localContactBall tau1382 center1382
def work1382 : RoundedTauEval :=
  evalTau precision tau1382 contact1382 logTwoBall

theorem center_sq1382 : (center1382.re : ℝ)^2 +
    (center1382.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1382]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1382 : work1382.theta.ok = true ∧
    work1382.jac.invOK = true ∧ acceptsUnitSq work1382.out = true := by
  norm_num [work1382, contact1382, tau1382, center1382, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1382 : CellCertificate where
  tauBall := tau1382
  contactCenter := center1382
  contactBall := contact1382
  work := work1382
  center_sq := center_sq1382
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1382.1
  jac_ok := checks1382.2.1
  accepted := checks1382.2.2

def tau1383 : RatBall :=
  ⟨⟨-53/320, -109/320⟩, 3/640⟩
def center1383 : GaussianRat :=
  ⟨-25685587/200000000, -238002417/1000000000⟩
def contact1383 : RatBall := localContactBall tau1383 center1383
def work1383 : RoundedTauEval :=
  evalTau precision tau1383 contact1383 logTwoBall

theorem center_sq1383 : (center1383.re : ℝ)^2 +
    (center1383.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1383]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1383 : work1383.theta.ok = true ∧
    work1383.jac.invOK = true ∧ acceptsUnitSq work1383.out = true := by
  norm_num [work1383, contact1383, tau1383, center1383, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1383 : CellCertificate where
  tauBall := tau1383
  contactCenter := center1383
  contactBall := contact1383
  work := work1383
  center_sq := center_sq1383
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1383.1
  jac_ok := checks1383.2.1
  accepted := checks1383.2.2

def cells : List CellCertificate := [cell1376, cell1377, cell1378, cell1379, cell1380, cell1381, cell1382, cell1383]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172
