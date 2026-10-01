import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1704 : RatBall :=
  ⟨⟨63/320, -109/320⟩, 3/640⟩
def center1704 : GaussianRat :=
  ⟨75841877/500000000, -234745077/1000000000⟩
def contact1704 : RatBall := localContactBall tau1704 center1704
def work1704 : RoundedTauEval :=
  evalTau precision tau1704 contact1704 logTwoBall

theorem center_sq1704 : (center1704.re : ℝ)^2 +
    (center1704.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1704]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1704 : work1704.theta.ok = true ∧
    work1704.jac.invOK = true ∧ acceptsUnitSq work1704.out = true := by
  norm_num [work1704, contact1704, tau1704, center1704, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1704 : CellCertificate where
  tauBall := tau1704
  contactCenter := center1704
  contactBall := contact1704
  work := work1704
  center_sq := center_sq1704
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1704.1
  jac_ok := checks1704.2.1
  accepted := checks1704.2.2

def tau1705 : RatBall :=
  ⟨⟨57/320, -107/320⟩, 3/640⟩
def center1705 : GaussianRat :=
  ⟨6857441/50000000, -46420737/200000000⟩
def contact1705 : RatBall := localContactBall tau1705 center1705
def work1705 : RoundedTauEval :=
  evalTau precision tau1705 contact1705 logTwoBall

theorem center_sq1705 : (center1705.re : ℝ)^2 +
    (center1705.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1705]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1705 : work1705.theta.ok = true ∧
    work1705.jac.invOK = true ∧ acceptsUnitSq work1705.out = true := by
  norm_num [work1705, contact1705, tau1705, center1705, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1705 : CellCertificate where
  tauBall := tau1705
  contactCenter := center1705
  contactBall := contact1705
  work := work1705
  center_sq := center_sq1705
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1705.1
  jac_ok := checks1705.2.1
  accepted := checks1705.2.2

def tau1706 : RatBall :=
  ⟨⟨59/320, -107/320⟩, 3/640⟩
def center1706 : GaussianRat :=
  ⟨141782257/1000000000, -231469249/1000000000⟩
def contact1706 : RatBall := localContactBall tau1706 center1706
def work1706 : RoundedTauEval :=
  evalTau precision tau1706 contact1706 logTwoBall

theorem center_sq1706 : (center1706.re : ℝ)^2 +
    (center1706.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1706]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1706 : work1706.theta.ok = true ∧
    work1706.jac.invOK = true ∧ acceptsUnitSq work1706.out = true := by
  norm_num [work1706, contact1706, tau1706, center1706, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1706 : CellCertificate where
  tauBall := tau1706
  contactCenter := center1706
  contactBall := contact1706
  work := work1706
  center_sq := center_sq1706
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1706.1
  jac_ok := checks1706.2.1
  accepted := checks1706.2.2

def tau1707 : RatBall :=
  ⟨⟨57/320, -21/64⟩, 3/640⟩
def center1707 : GaussianRat :=
  ⟨136531833/1000000000, -227470663/1000000000⟩
def contact1707 : RatBall := localContactBall tau1707 center1707
def work1707 : RoundedTauEval :=
  evalTau precision tau1707 contact1707 logTwoBall

theorem center_sq1707 : (center1707.re : ℝ)^2 +
    (center1707.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1707]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1707 : work1707.theta.ok = true ∧
    work1707.jac.invOK = true ∧ acceptsUnitSq work1707.out = true := by
  norm_num [work1707, contact1707, tau1707, center1707, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1707 : CellCertificate where
  tauBall := tau1707
  contactCenter := center1707
  contactBall := contact1707
  work := work1707
  center_sq := center_sq1707
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1707.1
  jac_ok := checks1707.2.1
  accepted := checks1707.2.2

def tau1708 : RatBall :=
  ⟨⟨59/320, -21/64⟩, 3/640⟩
def center1708 : GaussianRat :=
  ⟨70573769/500000000, -113426637/500000000⟩
def contact1708 : RatBall := localContactBall tau1708 center1708
def work1708 : RoundedTauEval :=
  evalTau precision tau1708 contact1708 logTwoBall

theorem center_sq1708 : (center1708.re : ℝ)^2 +
    (center1708.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1708]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1708 : work1708.theta.ok = true ∧
    work1708.jac.invOK = true ∧ acceptsUnitSq work1708.out = true := by
  norm_num [work1708, contact1708, tau1708, center1708, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1708 : CellCertificate where
  tauBall := tau1708
  contactCenter := center1708
  contactBall := contact1708
  work := work1708
  center_sq := center_sq1708
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1708.1
  jac_ok := checks1708.2.1
  accepted := checks1708.2.2

def tau1709 : RatBall :=
  ⟨⟨61/320, -107/320⟩, 3/640⟩
def center1709 : GaussianRat :=
  ⟨146398251/1000000000, -115408523/500000000⟩
def contact1709 : RatBall := localContactBall tau1709 center1709
def work1709 : RoundedTauEval :=
  evalTau precision tau1709 contact1709 logTwoBall

theorem center_sq1709 : (center1709.re : ℝ)^2 +
    (center1709.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1709]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1709 : work1709.theta.ok = true ∧
    work1709.jac.invOK = true ∧ acceptsUnitSq work1709.out = true := by
  norm_num [work1709, contact1709, tau1709, center1709, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1709 : CellCertificate where
  tauBall := tau1709
  contactCenter := center1709
  contactBall := contact1709
  work := work1709
  center_sq := center_sq1709
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1709.1
  jac_ok := checks1709.2.1
  accepted := checks1709.2.2

def tau1710 : RatBall :=
  ⟨⟨63/320, -107/320⟩, 3/640⟩
def center1710 : GaussianRat :=
  ⟨150996377/1000000000, -230147447/1000000000⟩
def contact1710 : RatBall := localContactBall tau1710 center1710
def work1710 : RoundedTauEval :=
  evalTau precision tau1710 contact1710 logTwoBall

theorem center_sq1710 : (center1710.re : ℝ)^2 +
    (center1710.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1710]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1710 : work1710.theta.ok = true ∧
    work1710.jac.invOK = true ∧ acceptsUnitSq work1710.out = true := by
  norm_num [work1710, contact1710, tau1710, center1710, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1710 : CellCertificate where
  tauBall := tau1710
  contactCenter := center1710
  contactBall := contact1710
  work := work1710
  center_sq := center_sq1710
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1710.1
  jac_ok := checks1710.2.1
  accepted := checks1710.2.2

def tau1711 : RatBall :=
  ⟨⟨61/320, -21/64⟩, 3/640⟩
def center1711 : GaussianRat :=
  ⟨145746161/1000000000, -113109273/500000000⟩
def contact1711 : RatBall := localContactBall tau1711 center1711
def work1711 : RoundedTauEval :=
  evalTau precision tau1711 contact1711 logTwoBall

theorem center_sq1711 : (center1711.re : ℝ)^2 +
    (center1711.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1711]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1711 : work1711.theta.ok = true ∧
    work1711.jac.invOK = true ∧ acceptsUnitSq work1711.out = true := by
  norm_num [work1711, contact1711, tau1711, center1711, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1711 : CellCertificate where
  tauBall := tau1711
  contactCenter := center1711
  contactBall := contact1711
  work := work1711
  center_sq := center_sq1711
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1711.1
  jac_ok := checks1711.2.1
  accepted := checks1711.2.2

def cells : List CellCertificate := [cell1704, cell1705, cell1706, cell1707, cell1708, cell1709, cell1710, cell1711]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213
