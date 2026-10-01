import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1640 : RatBall :=
  ⟨⟨39/320, -113/320⟩, 3/640⟩
def center1640 : GaussianRat :=
  ⟨48071341/500000000, -251379737/1000000000⟩
def contact1640 : RatBall := localContactBall tau1640 center1640
def work1640 : RoundedTauEval :=
  evalTau precision tau1640 contact1640 logTwoBall

theorem center_sq1640 : (center1640.re : ℝ)^2 +
    (center1640.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1640]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1640 : work1640.theta.ok = true ∧
    work1640.jac.invOK = true ∧ acceptsUnitSq work1640.out = true := by
  norm_num [work1640, contact1640, tau1640, center1640, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1640 : CellCertificate where
  tauBall := tau1640
  contactCenter := center1640
  contactBall := contact1640
  work := work1640
  center_sq := center_sq1640
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1640.1
  jac_ok := checks1640.2.1
  accepted := checks1640.2.2

def tau1641 : RatBall :=
  ⟨⟨41/320, -23/64⟩, 3/640⟩
def center1641 : GaussianRat :=
  ⟨12686743/125000000, -255720023/1000000000⟩
def contact1641 : RatBall := localContactBall tau1641 center1641
def work1641 : RoundedTauEval :=
  evalTau precision tau1641 contact1641 logTwoBall

theorem center_sq1641 : (center1641.re : ℝ)^2 +
    (center1641.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1641]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1641 : work1641.theta.ok = true ∧
    work1641.jac.invOK = true ∧ acceptsUnitSq work1641.out = true := by
  norm_num [work1641, contact1641, tau1641, center1641, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1641 : CellCertificate where
  tauBall := tau1641
  contactCenter := center1641
  contactBall := contact1641
  work := work1641
  center_sq := center_sq1641
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1641.1
  jac_ok := checks1641.2.1
  accepted := checks1641.2.2

def tau1642 : RatBall :=
  ⟨⟨43/320, -23/64⟩, 3/640⟩
def center1642 : GaussianRat :=
  ⟨106336973/1000000000, -255184583/1000000000⟩
def contact1642 : RatBall := localContactBall tau1642 center1642
def work1642 : RoundedTauEval :=
  evalTau precision tau1642 contact1642 logTwoBall

theorem center_sq1642 : (center1642.re : ℝ)^2 +
    (center1642.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1642]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1642 : work1642.theta.ok = true ∧
    work1642.jac.invOK = true ∧ acceptsUnitSq work1642.out = true := by
  norm_num [work1642, contact1642, tau1642, center1642, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1642 : CellCertificate where
  tauBall := tau1642
  contactCenter := center1642
  contactBall := contact1642
  work := work1642
  center_sq := center_sq1642
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1642.1
  jac_ok := checks1642.2.1
  accepted := checks1642.2.2

def tau1643 : RatBall :=
  ⟨⟨41/320, -113/320⟩, 3/640⟩
def center1643 : GaussianRat :=
  ⟨100977067/1000000000, -250881183/1000000000⟩
def contact1643 : RatBall := localContactBall tau1643 center1643
def work1643 : RoundedTauEval :=
  evalTau precision tau1643 contact1643 logTwoBall

theorem center_sq1643 : (center1643.re : ℝ)^2 +
    (center1643.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1643]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1643 : work1643.theta.ok = true ∧
    work1643.jac.invOK = true ∧ acceptsUnitSq work1643.out = true := by
  norm_num [work1643, contact1643, tau1643, center1643, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1643 : CellCertificate where
  tauBall := tau1643
  contactCenter := center1643
  contactBall := contact1643
  work := work1643
  center_sq := center_sq1643
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1643.1
  jac_ok := checks1643.2.1
  accepted := checks1643.2.2

def tau1644 : RatBall :=
  ⟨⟨43/320, -113/320⟩, 3/640⟩
def center1644 : GaussianRat :=
  ⟨105797499/1000000000, -62590039/250000000⟩
def contact1644 : RatBall := localContactBall tau1644 center1644
def work1644 : RoundedTauEval :=
  evalTau precision tau1644 contact1644 logTwoBall

theorem center_sq1644 : (center1644.re : ℝ)^2 +
    (center1644.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1644]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1644 : work1644.theta.ok = true ∧
    work1644.jac.invOK = true ∧ acceptsUnitSq work1644.out = true := by
  norm_num [work1644, contact1644, tau1644, center1644, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1644 : CellCertificate where
  tauBall := tau1644
  contactCenter := center1644
  contactBall := contact1644
  work := work1644
  center_sq := center_sq1644
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1644.1
  jac_ok := checks1644.2.1
  accepted := checks1644.2.2

def tau1645 : RatBall :=
  ⟨⟨9/64, -23/64⟩, 3/640⟩
def center1645 : GaussianRat :=
  ⟨889321/8000000, -254626433/1000000000⟩
def contact1645 : RatBall := localContactBall tau1645 center1645
def work1645 : RoundedTauEval :=
  evalTau precision tau1645 contact1645 logTwoBall

theorem center_sq1645 : (center1645.re : ℝ)^2 +
    (center1645.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1645]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1645 : work1645.theta.ok = true ∧
    work1645.jac.invOK = true ∧ acceptsUnitSq work1645.out = true := by
  norm_num [work1645, contact1645, tau1645, center1645, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1645 : CellCertificate where
  tauBall := tau1645
  contactCenter := center1645
  contactBall := contact1645
  work := work1645
  center_sq := center_sq1645
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1645.1
  jac_ok := checks1645.2.1
  accepted := checks1645.2.2

def tau1646 : RatBall :=
  ⟨⟨9/64, -113/320⟩, 3/640⟩
def center1646 : GaussianRat :=
  ⟨22120681/200000000, -249816993/1000000000⟩
def contact1646 : RatBall := localContactBall tau1646 center1646
def work1646 : RoundedTauEval :=
  evalTau precision tau1646 contact1646 logTwoBall

theorem center_sq1646 : (center1646.re : ℝ)^2 +
    (center1646.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1646]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1646 : work1646.theta.ok = true ∧
    work1646.jac.invOK = true ∧ acceptsUnitSq work1646.out = true := by
  norm_num [work1646, contact1646, tau1646, center1646, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1646 : CellCertificate where
  tauBall := tau1646
  contactCenter := center1646
  contactBall := contact1646
  work := work1646
  center_sq := center_sq1646
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1646.1
  jac_ok := checks1646.2.1
  accepted := checks1646.2.2

def tau1647 : RatBall :=
  ⟨⟨47/320, -113/320⟩, 3/640⟩
def center1647 : GaussianRat :=
  ⟨115394221/1000000000, -124626021/500000000⟩
def contact1647 : RatBall := localContactBall tau1647 center1647
def work1647 : RoundedTauEval :=
  evalTau precision tau1647 contact1647 logTwoBall

theorem center_sq1647 : (center1647.re : ℝ)^2 +
    (center1647.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1647]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1647 : work1647.theta.ok = true ∧
    work1647.jac.invOK = true ∧ acceptsUnitSq work1647.out = true := by
  norm_num [work1647, contact1647, tau1647, center1647, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1647 : CellCertificate where
  tauBall := tau1647
  contactCenter := center1647
  contactBall := contact1647
  work := work1647
  center_sq := center_sq1647
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1647.1
  jac_ok := checks1647.2.1
  accepted := checks1647.2.2

def cells : List CellCertificate := [cell1640, cell1641, cell1642, cell1643, cell1644, cell1645, cell1646, cell1647]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205
