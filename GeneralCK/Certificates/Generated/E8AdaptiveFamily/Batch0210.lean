import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1680 : RatBall :=
  ⟨⟨47/320, -103/320⟩, 3/640⟩
def center1680 : GaussianRat :=
  ⟨704399/6250000, -112796733/500000000⟩
def contact1680 : RatBall := localContactBall tau1680 center1680
def work1680 : RoundedTauEval :=
  evalTau precision tau1680 contact1680 logTwoBall

theorem center_sq1680 : (center1680.re : ℝ)^2 +
    (center1680.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1680]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1680 : work1680.theta.ok = true ∧
    work1680.jac.invOK = true ∧ acceptsUnitSq work1680.out = true := by
  norm_num [work1680, contact1680, tau1680, center1680, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1680 : CellCertificate where
  tauBall := tau1680
  contactCenter := center1680
  contactBall := contact1680
  work := work1680
  center_sq := center_sq1680
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1680.1
  jac_ok := checks1680.2.1
  accepted := checks1680.2.2

def tau1681 : RatBall :=
  ⟨⟨9/64, -101/320⟩, 3/640⟩
def center1681 : GaussianRat :=
  ⟨53769161/500000000, -221399049/1000000000⟩
def contact1681 : RatBall := localContactBall tau1681 center1681
def work1681 : RoundedTauEval :=
  evalTau precision tau1681 contact1681 logTwoBall

theorem center_sq1681 : (center1681.re : ℝ)^2 +
    (center1681.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1681]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1681 : work1681.theta.ok = true ∧
    work1681.jac.invOK = true ∧ acceptsUnitSq work1681.out = true := by
  norm_num [work1681, contact1681, tau1681, center1681, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1681 : CellCertificate where
  tauBall := tau1681
  contactCenter := center1681
  contactBall := contact1681
  work := work1681
  center_sq := center_sq1681
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1681.1
  jac_ok := checks1681.2.1
  accepted := checks1681.2.2

def tau1682 : RatBall :=
  ⟨⟨47/320, -101/320⟩, 3/640⟩
def center1682 : GaussianRat :=
  ⟨112208983/1000000000, -220920311/1000000000⟩
def contact1682 : RatBall := localContactBall tau1682 center1682
def work1682 : RoundedTauEval :=
  evalTau precision tau1682 contact1682 logTwoBall

theorem center_sq1682 : (center1682.re : ℝ)^2 +
    (center1682.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1682]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1682 : work1682.theta.ok = true ∧
    work1682.jac.invOK = true ∧ acceptsUnitSq work1682.out = true := by
  norm_num [work1682, contact1682, tau1682, center1682, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1682 : CellCertificate where
  tauBall := tau1682
  contactCenter := center1682
  contactBall := contact1682
  work := work1682
  center_sq := center_sq1682
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1682.1
  jac_ok := checks1682.2.1
  accepted := checks1682.2.2

def tau1683 : RatBall :=
  ⟨⟨49/320, -111/320⟩, 3/640⟩
def center1683 : GaussianRat :=
  ⟨29895113/250000000, -121954461/500000000⟩
def contact1683 : RatBall := localContactBall tau1683 center1683
def work1683 : RoundedTauEval :=
  evalTau precision tau1683 contact1683 logTwoBall

theorem center_sq1683 : (center1683.re : ℝ)^2 +
    (center1683.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1683]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1683 : work1683.theta.ok = true ∧
    work1683.jac.invOK = true ∧ acceptsUnitSq work1683.out = true := by
  norm_num [work1683, contact1683, tau1683, center1683, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1683 : CellCertificate where
  tauBall := tau1683
  contactCenter := center1683
  contactBall := contact1683
  work := work1683
  center_sq := center_sq1683
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1683.1
  jac_ok := checks1683.2.1
  accepted := checks1683.2.2

def tau1684 : RatBall :=
  ⟨⟨51/320, -111/320⟩, 3/640⟩
def center1684 : GaussianRat :=
  ⟨124318847/1000000000, -121658863/500000000⟩
def contact1684 : RatBall := localContactBall tau1684 center1684
def work1684 : RoundedTauEval :=
  evalTau precision tau1684 contact1684 logTwoBall

theorem center_sq1684 : (center1684.re : ℝ)^2 +
    (center1684.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1684]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1684 : work1684.theta.ok = true ∧
    work1684.jac.invOK = true ∧ acceptsUnitSq work1684.out = true := by
  norm_num [work1684, contact1684, tau1684, center1684, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1684 : CellCertificate where
  tauBall := tau1684
  contactCenter := center1684
  contactBall := contact1684
  work := work1684
  center_sq := center_sq1684
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1684.1
  jac_ok := checks1684.2.1
  accepted := checks1684.2.2

def tau1685 : RatBall :=
  ⟨⟨49/320, -109/320⟩, 3/640⟩
def center1685 : GaussianRat :=
  ⟨119007309/1000000000, -59793181/250000000⟩
def contact1685 : RatBall := localContactBall tau1685 center1685
def work1685 : RoundedTauEval :=
  evalTau precision tau1685 contact1685 logTwoBall

theorem center_sq1685 : (center1685.re : ℝ)^2 +
    (center1685.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1685]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1685 : work1685.theta.ok = true ∧
    work1685.jac.invOK = true ∧ acceptsUnitSq work1685.out = true := by
  norm_num [work1685, contact1685, tau1685, center1685, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1685 : CellCertificate where
  tauBall := tau1685
  contactCenter := center1685
  contactBall := contact1685
  work := work1685
  center_sq := center_sq1685
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1685.1
  jac_ok := checks1685.2.1
  accepted := checks1685.2.2

def tau1686 : RatBall :=
  ⟨⟨51/320, -109/320⟩, 3/640⟩
def center1686 : GaussianRat :=
  ⟨61862799/500000000, -238597409/1000000000⟩
def contact1686 : RatBall := localContactBall tau1686 center1686
def work1686 : RoundedTauEval :=
  evalTau precision tau1686 contact1686 logTwoBall

theorem center_sq1686 : (center1686.re : ℝ)^2 +
    (center1686.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1686]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1686 : work1686.theta.ok = true ∧
    work1686.jac.invOK = true ∧ acceptsUnitSq work1686.out = true := by
  norm_num [work1686, contact1686, tau1686, center1686, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1686 : CellCertificate where
  tauBall := tau1686
  contactCenter := center1686
  contactBall := contact1686
  work := work1686
  center_sq := center_sq1686
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1686.1
  jac_ok := checks1686.2.1
  accepted := checks1686.2.2

def tau1687 : RatBall :=
  ⟨⟨53/320, -111/320⟩, 3/640⟩
def center1687 : GaussianRat :=
  ⟨4032529/31250000, -121353177/500000000⟩
def contact1687 : RatBall := localContactBall tau1687 center1687
def work1687 : RoundedTauEval :=
  evalTau precision tau1687 contact1687 logTwoBall

theorem center_sq1687 : (center1687.re : ℝ)^2 +
    (center1687.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1687]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1687 : work1687.theta.ok = true ∧
    work1687.jac.invOK = true ∧ acceptsUnitSq work1687.out = true := by
  norm_num [work1687, contact1687, tau1687, center1687, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1687 : CellCertificate where
  tauBall := tau1687
  contactCenter := center1687
  contactBall := contact1687
  work := work1687
  center_sq := center_sq1687
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1687.1
  jac_ok := checks1687.2.1
  accepted := checks1687.2.2

def cells : List CellCertificate := [cell1680, cell1681, cell1682, cell1683, cell1684, cell1685, cell1686, cell1687]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210
