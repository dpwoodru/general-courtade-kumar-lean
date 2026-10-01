import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0193

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1544 : RatBall :=
  ⟨⟨3/320, -121/320⟩, 3/640⟩
def center1544 : GaussianRat :=
  ⟨1907311/250000000, -69081087/250000000⟩
def contact1544 : RatBall := localContactBall tau1544 center1544
def work1544 : RoundedTauEval :=
  evalTau precision tau1544 contact1544 logTwoBall

theorem center_sq1544 : (center1544.re : ℝ)^2 +
    (center1544.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1544]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1544 : work1544.theta.ok = true ∧
    work1544.jac.invOK = true ∧ acceptsUnitSq work1544.out = true := by
  norm_num [work1544, contact1544, tau1544, center1544, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1544 : CellCertificate where
  tauBall := tau1544
  contactCenter := center1544
  contactBall := contact1544
  work := work1544
  center_sq := center_sq1544
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1544.1
  jac_ok := checks1544.2.1
  accepted := checks1544.2.2

def tau1545 : RatBall :=
  ⟨⟨1/64, -123/320⟩, 3/640⟩
def center1545 : GaussianRat :=
  ⟨12788043/1000000000, -281364591/1000000000⟩
def contact1545 : RatBall := localContactBall tau1545 center1545
def work1545 : RoundedTauEval :=
  evalTau precision tau1545 contact1545 logTwoBall

theorem center_sq1545 : (center1545.re : ℝ)^2 +
    (center1545.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1545]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1545 : work1545.theta.ok = true ∧
    work1545.jac.invOK = true ∧ acceptsUnitSq work1545.out = true := by
  norm_num [work1545, contact1545, tau1545, center1545, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1545 : CellCertificate where
  tauBall := tau1545
  contactCenter := center1545
  contactBall := contact1545
  work := work1545
  center_sq := center_sq1545
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1545.1
  jac_ok := checks1545.2.1
  accepted := checks1545.2.2

def tau1546 : RatBall :=
  ⟨⟨7/320, -123/320⟩, 3/640⟩
def center1546 : GaussianRat :=
  ⟨3580067/200000000, -8789831/31250000⟩
def contact1546 : RatBall := localContactBall tau1546 center1546
def work1546 : RoundedTauEval :=
  evalTau precision tau1546 contact1546 logTwoBall

theorem center_sq1546 : (center1546.re : ℝ)^2 +
    (center1546.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1546]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1546 : work1546.theta.ok = true ∧
    work1546.jac.invOK = true ∧ acceptsUnitSq work1546.out = true := by
  norm_num [work1546, contact1546, tau1546, center1546, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1546 : CellCertificate where
  tauBall := tau1546
  contactCenter := center1546
  contactBall := contact1546
  work := work1546
  center_sq := center_sq1546
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1546.1
  jac_ok := checks1546.2.1
  accepted := checks1546.2.2

def tau1547 : RatBall :=
  ⟨⟨1/64, -121/320⟩, 3/640⟩
def center1547 : GaussianRat :=
  ⟨254281/20000000, -276265959/1000000000⟩
def contact1547 : RatBall := localContactBall tau1547 center1547
def work1547 : RoundedTauEval :=
  evalTau precision tau1547 contact1547 logTwoBall

theorem center_sq1547 : (center1547.re : ℝ)^2 +
    (center1547.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1547]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1547 : work1547.theta.ok = true ∧
    work1547.jac.invOK = true ∧ acceptsUnitSq work1547.out = true := by
  norm_num [work1547, contact1547, tau1547, center1547, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1547 : CellCertificate where
  tauBall := tau1547
  contactCenter := center1547
  contactBall := contact1547
  work := work1547
  center_sq := center_sq1547
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1547.1
  jac_ok := checks1547.2.1
  accepted := checks1547.2.2

def tau1548 : RatBall :=
  ⟨⟨7/320, -121/320⟩, 3/640⟩
def center1548 : GaussianRat :=
  ⟨2224603/125000000, -539411/1953125⟩
def contact1548 : RatBall := localContactBall tau1548 center1548
def work1548 : RoundedTauEval :=
  evalTau precision tau1548 contact1548 logTwoBall

theorem center_sq1548 : (center1548.re : ℝ)^2 +
    (center1548.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1548]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1548 : work1548.theta.ok = true ∧
    work1548.jac.invOK = true ∧ acceptsUnitSq work1548.out = true := by
  norm_num [work1548, contact1548, tau1548, center1548, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1548 : CellCertificate where
  tauBall := tau1548
  contactCenter := center1548
  contactBall := contact1548
  work := work1548
  center_sq := center_sq1548
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1548.1
  jac_ok := checks1548.2.1
  accepted := checks1548.2.2

def tau1549 : RatBall :=
  ⟨⟨9/320, -123/320⟩, 3/640⟩
def center1549 : GaussianRat :=
  ⟨11504853/500000000, -2811547/10000000⟩
def contact1549 : RatBall := localContactBall tau1549 center1549
def work1549 : RoundedTauEval :=
  evalTau precision tau1549 contact1549 logTwoBall

theorem center_sq1549 : (center1549.re : ℝ)^2 +
    (center1549.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1549]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1549 : work1549.theta.ok = true ∧
    work1549.jac.invOK = true ∧ acceptsUnitSq work1549.out = true := by
  norm_num [work1549, contact1549, tau1549, center1549, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1549 : CellCertificate where
  tauBall := tau1549
  contactCenter := center1549
  contactBall := contact1549
  work := work1549
  center_sq := center_sq1549
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1549.1
  jac_ok := checks1549.2.1
  accepted := checks1549.2.2

def tau1550 : RatBall :=
  ⟨⟨9/320, -121/320⟩, 3/640⟩
def center1550 : GaussianRat :=
  ⟨4575351/200000000, -276061831/1000000000⟩
def contact1550 : RatBall := localContactBall tau1550 center1550
def work1550 : RoundedTauEval :=
  evalTau precision tau1550 contact1550 logTwoBall

theorem center_sq1550 : (center1550.re : ℝ)^2 +
    (center1550.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1550]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1550 : work1550.theta.ok = true ∧
    work1550.jac.invOK = true ∧ acceptsUnitSq work1550.out = true := by
  norm_num [work1550, contact1550, tau1550, center1550, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1550 : CellCertificate where
  tauBall := tau1550
  contactCenter := center1550
  contactBall := contact1550
  work := work1550
  center_sq := center_sq1550
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1550.1
  jac_ok := checks1550.2.1
  accepted := checks1550.2.2

def tau1551 : RatBall :=
  ⟨⟨11/320, -121/320⟩, 3/640⟩
def center1551 : GaussianRat :=
  ⟨27953037/1000000000, -55183249/200000000⟩
def contact1551 : RatBall := localContactBall tau1551 center1551
def work1551 : RoundedTauEval :=
  evalTau precision tau1551 contact1551 logTwoBall

theorem center_sq1551 : (center1551.re : ℝ)^2 +
    (center1551.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1551]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1551 : work1551.theta.ok = true ∧
    work1551.jac.invOK = true ∧ acceptsUnitSq work1551.out = true := by
  norm_num [work1551, contact1551, tau1551, center1551, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1551 : CellCertificate where
  tauBall := tau1551
  contactCenter := center1551
  contactBall := contact1551
  work := work1551
  center_sq := center_sq1551
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1551.1
  jac_ok := checks1551.2.1
  accepted := checks1551.2.2

def cells : List CellCertificate := [cell1544, cell1545, cell1546, cell1547, cell1548, cell1549, cell1550, cell1551]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0193
