import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1464 : RatBall :=
  ⟨⟨-29/320, -23/64⟩, 3/640⟩
def center1464 : GaussianRat :=
  ⟨-4509823/62500000, -258436977/1000000000⟩
def contact1464 : RatBall := localContactBall tau1464 center1464
def work1464 : RoundedTauEval :=
  evalTau precision tau1464 contact1464 logTwoBall

theorem center_sq1464 : (center1464.re : ℝ)^2 +
    (center1464.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1464]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1464 : work1464.theta.ok = true ∧
    work1464.jac.invOK = true ∧ acceptsUnitSq work1464.out = true := by
  norm_num [work1464, contact1464, tau1464, center1464, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1464 : CellCertificate where
  tauBall := tau1464
  contactCenter := center1464
  contactBall := contact1464
  work := work1464
  center_sq := center_sq1464
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1464.1
  jac_ok := checks1464.2.1
  accepted := checks1464.2.2

def tau1465 : RatBall :=
  ⟨⟨-31/320, -113/320⟩, 3/640⟩
def center1465 : GaussianRat :=
  ⟨-15335517/200000000, -253142899/1000000000⟩
def contact1465 : RatBall := localContactBall tau1465 center1465
def work1465 : RoundedTauEval :=
  evalTau precision tau1465 contact1465 logTwoBall

theorem center_sq1465 : (center1465.re : ℝ)^2 +
    (center1465.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1465]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1465 : work1465.theta.ok = true ∧
    work1465.jac.invOK = true ∧ acceptsUnitSq work1465.out = true := by
  norm_num [work1465, contact1465, tau1465, center1465, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1465 : CellCertificate where
  tauBall := tau1465
  contactCenter := center1465
  contactBall := contact1465
  work := work1465
  center_sq := center_sq1465
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1465.1
  jac_ok := checks1465.2.1
  accepted := checks1465.2.2

def tau1466 : RatBall :=
  ⟨⟨-29/320, -113/320⟩, 3/640⟩
def center1466 : GaussianRat :=
  ⟨-1794563/25000000, -253524459/1000000000⟩
def contact1466 : RatBall := localContactBall tau1466 center1466
def work1466 : RoundedTauEval :=
  evalTau precision tau1466 contact1466 logTwoBall

theorem center_sq1466 : (center1466.re : ℝ)^2 +
    (center1466.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1466]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1466 : work1466.theta.ok = true ∧
    work1466.jac.invOK = true ∧ acceptsUnitSq work1466.out = true := by
  norm_num [work1466, contact1466, tau1466, center1466, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1466 : CellCertificate where
  tauBall := tau1466
  contactCenter := center1466
  contactBall := contact1466
  work := work1466
  center_sq := center_sq1466
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1466.1
  jac_ok := checks1466.2.1
  accepted := checks1466.2.2

def tau1467 : RatBall :=
  ⟨⟨-27/320, -23/64⟩, 3/640⟩
def center1467 : GaussianRat :=
  ⟨-67227179/1000000000, -258804339/1000000000⟩
def contact1467 : RatBall := localContactBall tau1467 center1467
def work1467 : RoundedTauEval :=
  evalTau precision tau1467 contact1467 logTwoBall

theorem center_sq1467 : (center1467.re : ℝ)^2 +
    (center1467.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1467]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1467 : work1467.theta.ok = true ∧
    work1467.jac.invOK = true ∧ acceptsUnitSq work1467.out = true := by
  norm_num [work1467, contact1467, tau1467, center1467, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1467 : CellCertificate where
  tauBall := tau1467
  contactCenter := center1467
  contactBall := contact1467
  work := work1467
  center_sq := center_sq1467
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1467.1
  jac_ok := checks1467.2.1
  accepted := checks1467.2.2

def tau1468 : RatBall :=
  ⟨⟨-5/64, -23/64⟩, 3/640⟩
def center1468 : GaussianRat :=
  ⟨-15571843/250000000, -51829311/200000000⟩
def contact1468 : RatBall := localContactBall tau1468 center1468
def work1468 : RoundedTauEval :=
  evalTau precision tau1468 contact1468 logTwoBall

theorem center_sq1468 : (center1468.re : ℝ)^2 +
    (center1468.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1468]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1468 : work1468.theta.ok = true ∧
    work1468.jac.invOK = true ∧ acceptsUnitSq work1468.out = true := by
  norm_num [work1468, contact1468, tau1468, center1468, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1468 : CellCertificate where
  tauBall := tau1468
  contactCenter := center1468
  contactBall := contact1468
  work := work1468
  center_sq := center_sq1468
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1468.1
  jac_ok := checks1468.2.1
  accepted := checks1468.2.2

def tau1469 : RatBall :=
  ⟨⟨-27/320, -113/320⟩, 3/640⟩
def center1469 : GaussianRat :=
  ⟨-33438609/500000000, -253881789/1000000000⟩
def contact1469 : RatBall := localContactBall tau1469 center1469
def work1469 : RoundedTauEval :=
  evalTau precision tau1469 contact1469 logTwoBall

theorem center_sq1469 : (center1469.re : ℝ)^2 +
    (center1469.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1469]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1469 : work1469.theta.ok = true ∧
    work1469.jac.invOK = true ∧ acceptsUnitSq work1469.out = true := by
  norm_num [work1469, contact1469, tau1469, center1469, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1469 : CellCertificate where
  tauBall := tau1469
  contactCenter := center1469
  contactBall := contact1469
  work := work1469
  center_sq := center_sq1469
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1469.1
  jac_ok := checks1469.2.1
  accepted := checks1469.2.2

def tau1470 : RatBall :=
  ⟨⟨-5/64, -113/320⟩, 3/640⟩
def center1470 : GaussianRat :=
  ⟨-61962339/1000000000, -63553661/250000000⟩
def contact1470 : RatBall := localContactBall tau1470 center1470
def work1470 : RoundedTauEval :=
  evalTau precision tau1470 contact1470 logTwoBall

theorem center_sq1470 : (center1470.re : ℝ)^2 +
    (center1470.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1470]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1470 : work1470.theta.ok = true ∧
    work1470.jac.invOK = true ∧ acceptsUnitSq work1470.out = true := by
  norm_num [work1470, contact1470, tau1470, center1470, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1470 : CellCertificate where
  tauBall := tau1470
  contactCenter := center1470
  contactBall := contact1470
  work := work1470
  center_sq := center_sq1470
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1470.1
  jac_ok := checks1470.2.1
  accepted := checks1470.2.2

def tau1471 : RatBall :=
  ⟨⟨-23/320, -119/320⟩, 3/640⟩
def center1471 : GaussianRat :=
  ⟨-14490933/250000000, -269422101/1000000000⟩
def contact1471 : RatBall := localContactBall tau1471 center1471
def work1471 : RoundedTauEval :=
  evalTau precision tau1471 contact1471 logTwoBall

theorem center_sq1471 : (center1471.re : ℝ)^2 +
    (center1471.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1471]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1471 : work1471.theta.ok = true ∧
    work1471.jac.invOK = true ∧ acceptsUnitSq work1471.out = true := by
  norm_num [work1471, contact1471, tau1471, center1471, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1471 : CellCertificate where
  tauBall := tau1471
  contactCenter := center1471
  contactBall := contact1471
  work := work1471
  center_sq := center_sq1471
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1471.1
  jac_ok := checks1471.2.1
  accepted := checks1471.2.2

def cells : List CellCertificate := [cell1464, cell1465, cell1466, cell1467, cell1468, cell1469, cell1470, cell1471]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183
