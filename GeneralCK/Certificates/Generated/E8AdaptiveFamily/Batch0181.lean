import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1448 : RatBall :=
  ⟨⟨-47/320, -103/320⟩, 3/640⟩
def center1448 : GaussianRat :=
  ⟨-704399/6250000, -112796733/500000000⟩
def contact1448 : RatBall := localContactBall tau1448 center1448
def work1448 : RoundedTauEval :=
  evalTau precision tau1448 contact1448 logTwoBall

theorem center_sq1448 : (center1448.re : ℝ)^2 +
    (center1448.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1448]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1448 : work1448.theta.ok = true ∧
    work1448.jac.invOK = true ∧ acceptsUnitSq work1448.out = true := by
  norm_num [work1448, contact1448, tau1448, center1448, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1448 : CellCertificate where
  tauBall := tau1448
  contactCenter := center1448
  contactBall := contact1448
  work := work1448
  center_sq := center_sq1448
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1448.1
  jac_ok := checks1448.2.1
  accepted := checks1448.2.2

def tau1449 : RatBall :=
  ⟨⟨-9/64, -103/320⟩, 3/640⟩
def center1449 : GaussianRat :=
  ⟨-21602887/200000000, -45217159/200000000⟩
def contact1449 : RatBall := localContactBall tau1449 center1449
def work1449 : RoundedTauEval :=
  evalTau precision tau1449 contact1449 logTwoBall

theorem center_sq1449 : (center1449.re : ℝ)^2 +
    (center1449.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1449]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1449 : work1449.theta.ok = true ∧
    work1449.jac.invOK = true ∧ acceptsUnitSq work1449.out = true := by
  norm_num [work1449, contact1449, tau1449, center1449, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1449 : CellCertificate where
  tauBall := tau1449
  contactCenter := center1449
  contactBall := contact1449
  work := work1449
  center_sq := center_sq1449
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1449.1
  jac_ok := checks1449.2.1
  accepted := checks1449.2.2

def tau1450 : RatBall :=
  ⟨⟨-47/320, -101/320⟩, 3/640⟩
def center1450 : GaussianRat :=
  ⟨-112208983/1000000000, -220920311/1000000000⟩
def contact1450 : RatBall := localContactBall tau1450 center1450
def work1450 : RoundedTauEval :=
  evalTau precision tau1450 contact1450 logTwoBall

theorem center_sq1450 : (center1450.re : ℝ)^2 +
    (center1450.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1450]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1450 : work1450.theta.ok = true ∧
    work1450.jac.invOK = true ∧ acceptsUnitSq work1450.out = true := by
  norm_num [work1450, contact1450, tau1450, center1450, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1450 : CellCertificate where
  tauBall := tau1450
  contactCenter := center1450
  contactBall := contact1450
  work := work1450
  center_sq := center_sq1450
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1450.1
  jac_ok := checks1450.2.1
  accepted := checks1450.2.2

def tau1451 : RatBall :=
  ⟨⟨-9/64, -101/320⟩, 3/640⟩
def center1451 : GaussianRat :=
  ⟨-53769161/500000000, -221399049/1000000000⟩
def contact1451 : RatBall := localContactBall tau1451 center1451
def work1451 : RoundedTauEval :=
  evalTau precision tau1451 contact1451 logTwoBall

theorem center_sq1451 : (center1451.re : ℝ)^2 +
    (center1451.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1451]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1451 : work1451.theta.ok = true ∧
    work1451.jac.invOK = true ∧ acceptsUnitSq work1451.out = true := by
  norm_num [work1451, contact1451, tau1451, center1451, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1451 : CellCertificate where
  tauBall := tau1451
  contactCenter := center1451
  contactBall := contact1451
  work := work1451
  center_sq := center_sq1451
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1451.1
  jac_ok := checks1451.2.1
  accepted := checks1451.2.2

def tau1452 : RatBall :=
  ⟨⟨-21/320, -121/320⟩, 3/640⟩
def center1452 : GaussianRat :=
  ⟨-53251841/1000000000, -54951623/200000000⟩
def contact1452 : RatBall := localContactBall tau1452 center1452
def work1452 : RoundedTauEval :=
  evalTau precision tau1452 contact1452 logTwoBall

theorem center_sq1452 : (center1452.re : ℝ)^2 +
    (center1452.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1452]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1452 : work1452.theta.ok = true ∧
    work1452.jac.invOK = true ∧ acceptsUnitSq work1452.out = true := by
  norm_num [work1452, contact1452, tau1452, center1452, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1452 : CellCertificate where
  tauBall := tau1452
  contactCenter := center1452
  contactBall := contact1452
  work := work1452
  center_sq := center_sq1452
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1452.1
  jac_ok := checks1452.2.1
  accepted := checks1452.2.2

def tau1453 : RatBall :=
  ⟨⟨-19/320, -121/320⟩, 3/640⟩
def center1453 : GaussianRat :=
  ⟨-48205717/1000000000, -275046561/1000000000⟩
def contact1453 : RatBall := localContactBall tau1453 center1453
def work1453 : RoundedTauEval :=
  evalTau precision tau1453 contact1453 logTwoBall

theorem center_sq1453 : (center1453.re : ℝ)^2 +
    (center1453.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1453]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1453 : work1453.theta.ok = true ∧
    work1453.jac.invOK = true ∧ acceptsUnitSq work1453.out = true := by
  norm_num [work1453, contact1453, tau1453, center1453, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1453 : CellCertificate where
  tauBall := tau1453
  contactCenter := center1453
  contactBall := contact1453
  work := work1453
  center_sq := center_sq1453
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1453.1
  jac_ok := checks1453.2.1
  accepted := checks1453.2.2

def tau1454 : RatBall :=
  ⟨⟨-17/320, -121/320⟩, 3/640⟩
def center1454 : GaussianRat :=
  ⟨-8630399/200000000, -275306779/1000000000⟩
def contact1454 : RatBall := localContactBall tau1454 center1454
def work1454 : RoundedTauEval :=
  evalTau precision tau1454 contact1454 logTwoBall

theorem center_sq1454 : (center1454.re : ℝ)^2 +
    (center1454.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1454]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1454 : work1454.theta.ok = true ∧
    work1454.jac.invOK = true ∧ acceptsUnitSq work1454.out = true := by
  norm_num [work1454, contact1454, tau1454, center1454, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1454 : CellCertificate where
  tauBall := tau1454
  contactCenter := center1454
  contactBall := contact1454
  work := work1454
  center_sq := center_sq1454
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1454.1
  jac_ok := checks1454.2.1
  accepted := checks1454.2.2

def tau1455 : RatBall :=
  ⟨⟨-31/320, -119/320⟩, 3/640⟩
def center1455 : GaussianRat :=
  ⟨-77908577/1000000000, -267922911/1000000000⟩
def contact1455 : RatBall := localContactBall tau1455 center1455
def work1455 : RoundedTauEval :=
  evalTau precision tau1455 contact1455 logTwoBall

theorem center_sq1455 : (center1455.re : ℝ)^2 +
    (center1455.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1455]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1455 : work1455.theta.ok = true ∧
    work1455.jac.invOK = true ∧ acceptsUnitSq work1455.out = true := by
  norm_num [work1455, contact1455, tau1455, center1455, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1455 : CellCertificate where
  tauBall := tau1455
  contactCenter := center1455
  contactBall := contact1455
  work := work1455
  center_sq := center_sq1455
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1455.1
  jac_ok := checks1455.2.1
  accepted := checks1455.2.2

def cells : List CellCertificate := [cell1448, cell1449, cell1450, cell1451, cell1452, cell1453, cell1454, cell1455]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181
