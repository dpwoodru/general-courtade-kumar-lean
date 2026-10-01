import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1504 : RatBall :=
  ⟨⟨-11/320, -119/320⟩, 3/640⟩
def center1504 : GaussianRat :=
  ⟨-27795199/1000000000, -135428181/500000000⟩
def contact1504 : RatBall := localContactBall tau1504 center1504
def work1504 : RoundedTauEval :=
  evalTau precision tau1504 contact1504 logTwoBall

theorem center_sq1504 : (center1504.re : ℝ)^2 +
    (center1504.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1504]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1504 : work1504.theta.ok = true ∧
    work1504.jac.invOK = true ∧ acceptsUnitSq work1504.out = true := by
  norm_num [work1504, contact1504, tau1504, center1504, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1504 : CellCertificate where
  tauBall := tau1504
  contactCenter := center1504
  contactBall := contact1504
  work := work1504
  center_sq := center_sq1504
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1504.1
  jac_ok := checks1504.2.1
  accepted := checks1504.2.2

def tau1505 : RatBall :=
  ⟨⟨-9/320, -119/320⟩, 3/640⟩
def center1505 : GaussianRat :=
  ⟨-22747453/1000000000, -270997951/1000000000⟩
def contact1505 : RatBall := localContactBall tau1505 center1505
def work1505 : RoundedTauEval :=
  evalTau precision tau1505 contact1505 logTwoBall

theorem center_sq1505 : (center1505.re : ℝ)^2 +
    (center1505.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1505]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1505 : work1505.theta.ok = true ∧
    work1505.jac.invOK = true ∧ acceptsUnitSq work1505.out = true := by
  norm_num [work1505, contact1505, tau1505, center1505, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1505 : CellCertificate where
  tauBall := tau1505
  contactCenter := center1505
  contactBall := contact1505
  work := work1505
  center_sq := center_sq1505
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1505.1
  jac_ok := checks1505.2.1
  accepted := checks1505.2.2

def tau1506 : RatBall :=
  ⟨⟨-11/320, -117/320⟩, 3/640⟩
def center1506 : GaussianRat :=
  ⟨-863803/31250000, -33228071/125000000⟩
def contact1506 : RatBall := localContactBall tau1506 center1506
def work1506 : RoundedTauEval :=
  evalTau precision tau1506 contact1506 logTwoBall

theorem center_sq1506 : (center1506.re : ℝ)^2 +
    (center1506.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1506]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1506 : work1506.theta.ok = true ∧
    work1506.jac.invOK = true ∧ acceptsUnitSq work1506.out = true := by
  norm_num [work1506, contact1506, tau1506, center1506, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1506 : CellCertificate where
  tauBall := tau1506
  contactCenter := center1506
  contactBall := contact1506
  work := work1506
  center_sq := center_sq1506
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1506.1
  jac_ok := checks1506.2.1
  accepted := checks1506.2.2

def tau1507 : RatBall :=
  ⟨⟨-9/320, -117/320⟩, 3/640⟩
def center1507 : GaussianRat :=
  ⟨-4524341/200000000, -53192453/200000000⟩
def contact1507 : RatBall := localContactBall tau1507 center1507
def work1507 : RoundedTauEval :=
  evalTau precision tau1507 contact1507 logTwoBall

theorem center_sq1507 : (center1507.re : ℝ)^2 +
    (center1507.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1507]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1507 : work1507.theta.ok = true ∧
    work1507.jac.invOK = true ∧ acceptsUnitSq work1507.out = true := by
  norm_num [work1507, contact1507, tau1507, center1507, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1507 : CellCertificate where
  tauBall := tau1507
  contactCenter := center1507
  contactBall := contact1507
  work := work1507
  center_sq := center_sq1507
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1507.1
  jac_ok := checks1507.2.1
  accepted := checks1507.2.2

def tau1508 : RatBall :=
  ⟨⟨-3/64, -23/64⟩, 3/640⟩
def center1508 : GaussianRat :=
  ⟨-37465331/1000000000, -260472693/1000000000⟩
def contact1508 : RatBall := localContactBall tau1508 center1508
def work1508 : RoundedTauEval :=
  evalTau precision tau1508 contact1508 logTwoBall

theorem center_sq1508 : (center1508.re : ℝ)^2 +
    (center1508.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1508]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1508 : work1508.theta.ok = true ∧
    work1508.jac.invOK = true ∧ acceptsUnitSq work1508.out = true := by
  norm_num [work1508, contact1508, tau1508, center1508, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1508 : CellCertificate where
  tauBall := tau1508
  contactCenter := center1508
  contactBall := contact1508
  work := work1508
  center_sq := center_sq1508
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1508.1
  jac_ok := checks1508.2.1
  accepted := checks1508.2.2

def tau1509 : RatBall :=
  ⟨⟨-13/320, -23/64⟩, 3/640⟩
def center1509 : GaussianRat :=
  ⟨-32481297/1000000000, -260659621/1000000000⟩
def contact1509 : RatBall := localContactBall tau1509 center1509
def work1509 : RoundedTauEval :=
  evalTau precision tau1509 contact1509 logTwoBall

theorem center_sq1509 : (center1509.re : ℝ)^2 +
    (center1509.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1509]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1509 : work1509.theta.ok = true ∧
    work1509.jac.invOK = true ∧ acceptsUnitSq work1509.out = true := by
  norm_num [work1509, contact1509, tau1509, center1509, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1509 : CellCertificate where
  tauBall := tau1509
  contactCenter := center1509
  contactBall := contact1509
  work := work1509
  center_sq := center_sq1509
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1509.1
  jac_ok := checks1509.2.1
  accepted := checks1509.2.2

def tau1510 : RatBall :=
  ⟨⟨-3/64, -113/320⟩, 3/640⟩
def center1510 : GaussianRat :=
  ⟨-18633993/500000000, -15969023/62500000⟩
def contact1510 : RatBall := localContactBall tau1510 center1510
def work1510 : RoundedTauEval :=
  evalTau precision tau1510 contact1510 logTwoBall

theorem center_sq1510 : (center1510.re : ℝ)^2 +
    (center1510.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1510]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1510 : work1510.theta.ok = true ∧
    work1510.jac.invOK = true ∧ acceptsUnitSq work1510.out = true := by
  norm_num [work1510, contact1510, tau1510, center1510, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1510 : CellCertificate where
  tauBall := tau1510
  contactCenter := center1510
  contactBall := contact1510
  work := work1510
  center_sq := center_sq1510
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1510.1
  jac_ok := checks1510.2.1
  accepted := checks1510.2.2

def tau1511 : RatBall :=
  ⟨⟨-13/320, -113/320⟩, 3/640⟩
def center1511 : GaussianRat :=
  ⟨-32309979/1000000000, -127843073/500000000⟩
def contact1511 : RatBall := localContactBall tau1511 center1511
def work1511 : RoundedTauEval :=
  evalTau precision tau1511 contact1511 logTwoBall

theorem center_sq1511 : (center1511.re : ℝ)^2 +
    (center1511.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1511]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1511 : work1511.theta.ok = true ∧
    work1511.jac.invOK = true ∧ acceptsUnitSq work1511.out = true := by
  norm_num [work1511, contact1511, tau1511, center1511, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1511 : CellCertificate where
  tauBall := tau1511
  contactCenter := center1511
  contactBall := contact1511
  work := work1511
  center_sq := center_sq1511
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1511.1
  jac_ok := checks1511.2.1
  accepted := checks1511.2.2

def cells : List CellCertificate := [cell1504, cell1505, cell1506, cell1507, cell1508, cell1509, cell1510, cell1511]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188
