import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1488 : RatBall :=
  ⟨⟨-13/320, -121/320⟩, 3/640⟩
def center1488 : GaussianRat :=
  ⟨-8256217/250000000, -34467723/125000000⟩
def contact1488 : RatBall := localContactBall tau1488 center1488
def work1488 : RoundedTauEval :=
  evalTau precision tau1488 contact1488 logTwoBall

theorem center_sq1488 : (center1488.re : ℝ)^2 +
    (center1488.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1488]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1488 : work1488.theta.ok = true ∧
    work1488.jac.invOK = true ∧ acceptsUnitSq work1488.out = true := by
  norm_num [work1488, contact1488, tau1488, center1488, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1488 : CellCertificate where
  tauBall := tau1488
  contactCenter := center1488
  contactBall := contact1488
  work := work1488
  center_sq := center_sq1488
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1488.1
  jac_ok := checks1488.2.1
  accepted := checks1488.2.2

def tau1489 : RatBall :=
  ⟨⟨-9/320, -123/320⟩, 3/640⟩
def center1489 : GaussianRat :=
  ⟨-11504853/500000000, -2811547/10000000⟩
def contact1489 : RatBall := localContactBall tau1489 center1489
def work1489 : RoundedTauEval :=
  evalTau precision tau1489 contact1489 logTwoBall

theorem center_sq1489 : (center1489.re : ℝ)^2 +
    (center1489.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1489]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1489 : work1489.theta.ok = true ∧
    work1489.jac.invOK = true ∧ acceptsUnitSq work1489.out = true := by
  norm_num [work1489, contact1489, tau1489, center1489, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1489 : CellCertificate where
  tauBall := tau1489
  contactCenter := center1489
  contactBall := contact1489
  work := work1489
  center_sq := center_sq1489
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1489.1
  jac_ok := checks1489.2.1
  accepted := checks1489.2.2

def tau1490 : RatBall :=
  ⟨⟨-11/320, -121/320⟩, 3/640⟩
def center1490 : GaussianRat :=
  ⟨-27953037/1000000000, -55183249/200000000⟩
def contact1490 : RatBall := localContactBall tau1490 center1490
def work1490 : RoundedTauEval :=
  evalTau precision tau1490 contact1490 logTwoBall

theorem center_sq1490 : (center1490.re : ℝ)^2 +
    (center1490.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1490]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1490 : work1490.theta.ok = true ∧
    work1490.jac.invOK = true ∧ acceptsUnitSq work1490.out = true := by
  norm_num [work1490, contact1490, tau1490, center1490, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1490 : CellCertificate where
  tauBall := tau1490
  contactCenter := center1490
  contactBall := contact1490
  work := work1490
  center_sq := center_sq1490
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1490.1
  jac_ok := checks1490.2.1
  accepted := checks1490.2.2

def tau1491 : RatBall :=
  ⟨⟨-9/320, -121/320⟩, 3/640⟩
def center1491 : GaussianRat :=
  ⟨-4575351/200000000, -276061831/1000000000⟩
def contact1491 : RatBall := localContactBall tau1491 center1491
def work1491 : RoundedTauEval :=
  evalTau precision tau1491 contact1491 logTwoBall

theorem center_sq1491 : (center1491.re : ℝ)^2 +
    (center1491.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1491]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1491 : work1491.theta.ok = true ∧
    work1491.jac.invOK = true ∧ acceptsUnitSq work1491.out = true := by
  norm_num [work1491, contact1491, tau1491, center1491, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1491 : CellCertificate where
  tauBall := tau1491
  contactCenter := center1491
  contactBall := contact1491
  work := work1491
  center_sq := center_sq1491
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1491.1
  jac_ok := checks1491.2.1
  accepted := checks1491.2.2

def tau1492 : RatBall :=
  ⟨⟨-7/320, -123/320⟩, 3/640⟩
def center1492 : GaussianRat :=
  ⟨-3580067/200000000, -8789831/31250000⟩
def contact1492 : RatBall := localContactBall tau1492 center1492
def work1492 : RoundedTauEval :=
  evalTau precision tau1492 contact1492 logTwoBall

theorem center_sq1492 : (center1492.re : ℝ)^2 +
    (center1492.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1492]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1492 : work1492.theta.ok = true ∧
    work1492.jac.invOK = true ∧ acceptsUnitSq work1492.out = true := by
  norm_num [work1492, contact1492, tau1492, center1492, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1492 : CellCertificate where
  tauBall := tau1492
  contactCenter := center1492
  contactBall := contact1492
  work := work1492
  center_sq := center_sq1492
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1492.1
  jac_ok := checks1492.2.1
  accepted := checks1492.2.2

def tau1493 : RatBall :=
  ⟨⟨-1/64, -123/320⟩, 3/640⟩
def center1493 : GaussianRat :=
  ⟨-12788043/1000000000, -281364591/1000000000⟩
def contact1493 : RatBall := localContactBall tau1493 center1493
def work1493 : RoundedTauEval :=
  evalTau precision tau1493 contact1493 logTwoBall

theorem center_sq1493 : (center1493.re : ℝ)^2 +
    (center1493.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1493]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1493 : work1493.theta.ok = true ∧
    work1493.jac.invOK = true ∧ acceptsUnitSq work1493.out = true := by
  norm_num [work1493, contact1493, tau1493, center1493, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1493 : CellCertificate where
  tauBall := tau1493
  contactCenter := center1493
  contactBall := contact1493
  work := work1493
  center_sq := center_sq1493
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1493.1
  jac_ok := checks1493.2.1
  accepted := checks1493.2.2

def tau1494 : RatBall :=
  ⟨⟨-7/320, -121/320⟩, 3/640⟩
def center1494 : GaussianRat :=
  ⟨-2224603/125000000, -539411/1953125⟩
def contact1494 : RatBall := localContactBall tau1494 center1494
def work1494 : RoundedTauEval :=
  evalTau precision tau1494 contact1494 logTwoBall

theorem center_sq1494 : (center1494.re : ℝ)^2 +
    (center1494.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1494]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1494 : work1494.theta.ok = true ∧
    work1494.jac.invOK = true ∧ acceptsUnitSq work1494.out = true := by
  norm_num [work1494, contact1494, tau1494, center1494, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1494 : CellCertificate where
  tauBall := tau1494
  contactCenter := center1494
  contactBall := contact1494
  work := work1494
  center_sq := center_sq1494
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1494.1
  jac_ok := checks1494.2.1
  accepted := checks1494.2.2

def tau1495 : RatBall :=
  ⟨⟨-1/64, -121/320⟩, 3/640⟩
def center1495 : GaussianRat :=
  ⟨-254281/20000000, -276265959/1000000000⟩
def contact1495 : RatBall := localContactBall tau1495 center1495
def work1495 : RoundedTauEval :=
  evalTau precision tau1495 contact1495 logTwoBall

theorem center_sq1495 : (center1495.re : ℝ)^2 +
    (center1495.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1495]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1495 : work1495.theta.ok = true ∧
    work1495.jac.invOK = true ∧ acceptsUnitSq work1495.out = true := by
  norm_num [work1495, contact1495, tau1495, center1495, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1495 : CellCertificate where
  tauBall := tau1495
  contactCenter := center1495
  contactBall := contact1495
  work := work1495
  center_sq := center_sq1495
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1495.1
  jac_ok := checks1495.2.1
  accepted := checks1495.2.2

def cells : List CellCertificate := [cell1488, cell1489, cell1490, cell1491, cell1492, cell1493, cell1494, cell1495]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186
