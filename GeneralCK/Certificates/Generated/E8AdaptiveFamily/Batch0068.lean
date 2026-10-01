import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0544 : RatBall :=
  ⟨⟨-63/160, -13/160⟩, 3/320⟩
def center0544 : GaussianRat :=
  ⟨-260916819/1000000000, -48524207/1000000000⟩
def contact0544 : RatBall := localContactBall tau0544 center0544
def work0544 : RoundedTauEval :=
  evalTau precision tau0544 contact0544 logTwoBall

theorem center_sq0544 : (center0544.re : ℝ)^2 +
    (center0544.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0544]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0544 : work0544.theta.ok = true ∧
    work0544.jac.invOK = true ∧ acceptsUnitSq work0544.out = true := by
  norm_num [work0544, contact0544, tau0544, center0544, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0544 : CellCertificate where
  tauBall := tau0544
  contactCenter := center0544
  contactBall := contact0544
  work := work0544
  center_sq := center_sq0544
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0544.1
  jac_ok := checks0544.2.1
  accepted := checks0544.2.2

def tau0545 : RatBall :=
  ⟨⟨-61/160, -13/160⟩, 3/320⟩
def center0545 : GaussianRat :=
  ⟨-126702243/500000000, -6119291/125000000⟩
def contact0545 : RatBall := localContactBall tau0545 center0545
def work0545 : RoundedTauEval :=
  evalTau precision tau0545 contact0545 logTwoBall

theorem center_sq0545 : (center0545.re : ℝ)^2 +
    (center0545.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0545]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0545 : work0545.theta.ok = true ∧
    work0545.jac.invOK = true ∧ acceptsUnitSq work0545.out = true := by
  norm_num [work0545, contact0545, tau0545, center0545, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0545 : CellCertificate where
  tauBall := tau0545
  contactCenter := center0545
  contactBall := contact0545
  work := work0545
  center_sq := center_sq0545
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0545.1
  jac_ok := checks0545.2.1
  accepted := checks0545.2.2

def tau0546 : RatBall :=
  ⟨⟨-59/160, -3/32⟩, 3/320⟩
def center0546 : GaussianRat :=
  ⟨-246278271/1000000000, -56993771/1000000000⟩
def contact0546 : RatBall := localContactBall tau0546 center0546
def work0546 : RoundedTauEval :=
  evalTau precision tau0546 contact0546 logTwoBall

theorem center_sq0546 : (center0546.re : ℝ)^2 +
    (center0546.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0546]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0546 : work0546.theta.ok = true ∧
    work0546.jac.invOK = true ∧ acceptsUnitSq work0546.out = true := by
  norm_num [work0546, contact0546, tau0546, center0546, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0546 : CellCertificate where
  tauBall := tau0546
  contactCenter := center0546
  contactBall := contact0546
  work := work0546
  center_sq := center_sq0546
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0546.1
  jac_ok := checks0546.2.1
  accepted := checks0546.2.2

def tau0547 : RatBall :=
  ⟨⟨-57/160, -3/32⟩, 3/320⟩
def center0547 : GaussianRat :=
  ⟨-11931267/50000000, -14368881/250000000⟩
def contact0547 : RatBall := localContactBall tau0547 center0547
def work0547 : RoundedTauEval :=
  evalTau precision tau0547 contact0547 logTwoBall

theorem center_sq0547 : (center0547.re : ℝ)^2 +
    (center0547.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0547]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0547 : work0547.theta.ok = true ∧
    work0547.jac.invOK = true ∧ acceptsUnitSq work0547.out = true := by
  norm_num [work0547, contact0547, tau0547, center0547, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0547 : CellCertificate where
  tauBall := tau0547
  contactCenter := center0547
  contactBall := contact0547
  work := work0547
  center_sq := center_sq0547
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0547.1
  jac_ok := checks0547.2.1
  accepted := checks0547.2.2

def tau0548 : RatBall :=
  ⟨⟨-59/160, -13/160⟩, 3/320⟩
def center0548 : GaussianRat :=
  ⟨-245825343/1000000000, -12344447/250000000⟩
def contact0548 : RatBall := localContactBall tau0548 center0548
def work0548 : RoundedTauEval :=
  evalTau precision tau0548 contact0548 logTwoBall

theorem center_sq0548 : (center0548.re : ℝ)^2 +
    (center0548.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0548]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0548 : work0548.theta.ok = true ∧
    work0548.jac.invOK = true ∧ acceptsUnitSq work0548.out = true := by
  norm_num [work0548, contact0548, tau0548, center0548, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0548 : CellCertificate where
  tauBall := tau0548
  contactCenter := center0548
  contactBall := contact0548
  work := work0548
  center_sq := center_sq0548
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0548.1
  jac_ok := checks0548.2.1
  accepted := checks0548.2.2

def tau0549 : RatBall :=
  ⟨⟨-57/160, -13/160⟩, 3/320⟩
def center0549 : GaussianRat :=
  ⟨-238180443/1000000000, -24897027/500000000⟩
def contact0549 : RatBall := localContactBall tau0549 center0549
def work0549 : RoundedTauEval :=
  evalTau precision tau0549 contact0549 logTwoBall

theorem center_sq0549 : (center0549.re : ℝ)^2 +
    (center0549.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0549]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0549 : work0549.theta.ok = true ∧
    work0549.jac.invOK = true ∧ acceptsUnitSq work0549.out = true := by
  norm_num [work0549, contact0549, tau0549, center0549, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0549 : CellCertificate where
  tauBall := tau0549
  contactCenter := center0549
  contactBall := contact0549
  work := work0549
  center_sq := center_sq0549
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0549.1
  jac_ok := checks0549.2.1
  accepted := checks0549.2.2

def tau0550 : RatBall :=
  ⟨⟨-63/160, -11/160⟩, 3/320⟩
def center0550 : GaussianRat :=
  ⟨-260517353/1000000000, -1026213/25000000⟩
def contact0550 : RatBall := localContactBall tau0550 center0550
def work0550 : RoundedTauEval :=
  evalTau precision tau0550 contact0550 logTwoBall

theorem center_sq0550 : (center0550.re : ℝ)^2 +
    (center0550.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0550]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0550 : work0550.theta.ok = true ∧
    work0550.jac.invOK = true ∧ acceptsUnitSq work0550.out = true := by
  norm_num [work0550, contact0550, tau0550, center0550, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0550 : CellCertificate where
  tauBall := tau0550
  contactCenter := center0550
  contactBall := contact0550
  work := work0550
  center_sq := center_sq0550
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0550.1
  jac_ok := checks0550.2.1
  accepted := checks0550.2.2

def tau0551 : RatBall :=
  ⟨⟨-61/160, -11/160⟩, 3/320⟩
def center0551 : GaussianRat :=
  ⟨-25301093/100000000, -41411583/1000000000⟩
def contact0551 : RatBall := localContactBall tau0551 center0551
def work0551 : RoundedTauEval :=
  evalTau precision tau0551 contact0551 logTwoBall

theorem center_sq0551 : (center0551.re : ℝ)^2 +
    (center0551.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0551]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0551 : work0551.theta.ok = true ∧
    work0551.jac.invOK = true ∧ acceptsUnitSq work0551.out = true := by
  norm_num [work0551, contact0551, tau0551, center0551, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0551 : CellCertificate where
  tauBall := tau0551
  contactCenter := center0551
  contactBall := contact0551
  work := work0551
  center_sq := center_sq0551
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0551.1
  jac_ok := checks0551.2.1
  accepted := checks0551.2.2

def cells : List CellCertificate := [cell0544, cell0545, cell0546, cell0547, cell0548, cell0549, cell0550, cell0551]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068
