import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0218

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1744 : RatBall :=
  ⟨⟨73/320, -21/64⟩, 3/640⟩
def center1744 : GaussianRat :=
  ⟨172956611/1000000000, -222066431/1000000000⟩
def contact1744 : RatBall := localContactBall tau1744 center1744
def work1744 : RoundedTauEval :=
  evalTau precision tau1744 contact1744 logTwoBall

theorem center_sq1744 : (center1744.re : ℝ)^2 +
    (center1744.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1744]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1744 : work1744.theta.ok = true ∧
    work1744.jac.invOK = true ∧ acceptsUnitSq work1744.out = true := by
  norm_num [work1744, contact1744, tau1744, center1744, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1744 : CellCertificate where
  tauBall := tau1744
  contactCenter := center1744
  contactBall := contact1744
  work := work1744
  center_sq := center_sq1744
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1744.1
  jac_ok := checks1744.2.1
  accepted := checks1744.2.2

def tau1745 : RatBall :=
  ⟨⟨13/64, -103/320⟩, 3/640⟩
def center1745 : GaussianRat :=
  ⟨154223071/1000000000, -110176223/500000000⟩
def contact1745 : RatBall := localContactBall tau1745 center1745
def work1745 : RoundedTauEval :=
  evalTau precision tau1745 contact1745 logTwoBall

theorem center_sq1745 : (center1745.re : ℝ)^2 +
    (center1745.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1745]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1745 : work1745.theta.ok = true ∧
    work1745.jac.invOK = true ∧ acceptsUnitSq work1745.out = true := by
  norm_num [work1745, contact1745, tau1745, center1745, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1745 : CellCertificate where
  tauBall := tau1745
  contactCenter := center1745
  contactBall := contact1745
  work := work1745
  center_sq := center_sq1745
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1745.1
  jac_ok := checks1745.2.1
  accepted := checks1745.2.2

def tau1746 : RatBall :=
  ⟨⟨67/320, -103/320⟩, 3/640⟩
def center1746 : GaussianRat :=
  ⟨79376053/500000000, -109843089/500000000⟩
def contact1746 : RatBall := localContactBall tau1746 center1746
def work1746 : RoundedTauEval :=
  evalTau precision tau1746 contact1746 logTwoBall

theorem center_sq1746 : (center1746.re : ℝ)^2 +
    (center1746.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1746]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1746 : work1746.theta.ok = true ∧
    work1746.jac.invOK = true ∧ acceptsUnitSq work1746.out = true := by
  norm_num [work1746, contact1746, tau1746, center1746, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1746 : CellCertificate where
  tauBall := tau1746
  contactCenter := center1746
  contactBall := contact1746
  work := work1746
  center_sq := center_sq1746
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1746.1
  jac_ok := checks1746.2.1
  accepted := checks1746.2.2

def tau1747 : RatBall :=
  ⟨⟨13/64, -101/320⟩, 3/640⟩
def center1747 : GaussianRat :=
  ⟨38393397/250000000, -26977781/125000000⟩
def contact1747 : RatBall := localContactBall tau1747 center1747
def work1747 : RoundedTauEval :=
  evalTau precision tau1747 contact1747 logTwoBall

theorem center_sq1747 : (center1747.re : ℝ)^2 +
    (center1747.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1747]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1747 : work1747.theta.ok = true ∧
    work1747.jac.invOK = true ∧ acceptsUnitSq work1747.out = true := by
  norm_num [work1747, contact1747, tau1747, center1747, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1747 : CellCertificate where
  tauBall := tau1747
  contactCenter := center1747
  contactBall := contact1747
  work := work1747
  center_sq := center_sq1747
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1747.1
  jac_ok := checks1747.2.1
  accepted := checks1747.2.2

def tau1748 : RatBall :=
  ⟨⟨67/320, -101/320⟩, 3/640⟩
def center1748 : GaussianRat :=
  ⟨158087121/1000000000, -215173931/1000000000⟩
def contact1748 : RatBall := localContactBall tau1748 center1748
def work1748 : RoundedTauEval :=
  evalTau precision tau1748 contact1748 logTwoBall

theorem center_sq1748 : (center1748.re : ℝ)^2 +
    (center1748.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1748]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1748 : work1748.theta.ok = true ∧
    work1748.jac.invOK = true ∧ acceptsUnitSq work1748.out = true := by
  norm_num [work1748, contact1748, tau1748, center1748, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1748 : CellCertificate where
  tauBall := tau1748
  contactCenter := center1748
  contactBall := contact1748
  work := work1748
  center_sq := center_sq1748
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1748.1
  jac_ok := checks1748.2.1
  accepted := checks1748.2.2

def tau1749 : RatBall :=
  ⟨⟨69/320, -103/320⟩, 3/640⟩
def center1749 : GaussianRat :=
  ⟨40815707/250000000, -219004401/1000000000⟩
def contact1749 : RatBall := localContactBall tau1749 center1749
def work1749 : RoundedTauEval :=
  evalTau precision tau1749 contact1749 logTwoBall

theorem center_sq1749 : (center1749.re : ℝ)^2 +
    (center1749.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1749]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1749 : work1749.theta.ok = true ∧
    work1749.jac.invOK = true ∧ acceptsUnitSq work1749.out = true := by
  norm_num [work1749, contact1749, tau1749, center1749, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1749 : CellCertificate where
  tauBall := tau1749
  contactCenter := center1749
  contactBall := contact1749
  work := work1749
  center_sq := center_sq1749
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1749.1
  jac_ok := checks1749.2.1
  accepted := checks1749.2.2

def tau1750 : RatBall :=
  ⟨⟨71/320, -103/320⟩, 3/640⟩
def center1750 : GaussianRat :=
  ⟨83877437/500000000, -218307477/1000000000⟩
def contact1750 : RatBall := localContactBall tau1750 center1750
def work1750 : RoundedTauEval :=
  evalTau precision tau1750 contact1750 logTwoBall

theorem center_sq1750 : (center1750.re : ℝ)^2 +
    (center1750.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1750]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1750 : work1750.theta.ok = true ∧
    work1750.jac.invOK = true ∧ acceptsUnitSq work1750.out = true := by
  norm_num [work1750, contact1750, tau1750, center1750, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1750 : CellCertificate where
  tauBall := tau1750
  contactCenter := center1750
  contactBall := contact1750
  work := work1750
  center_sq := center_sq1750
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1750.1
  jac_ok := checks1750.2.1
  accepted := checks1750.2.2

def tau1751 : RatBall :=
  ⟨⟨69/320, -101/320⟩, 3/640⟩
def center1751 : GaussianRat :=
  ⟨32516539/200000000, -26813809/125000000⟩
def contact1751 : RatBall := localContactBall tau1751 center1751
def work1751 : RoundedTauEval :=
  evalTau precision tau1751 contact1751 logTwoBall

theorem center_sq1751 : (center1751.re : ℝ)^2 +
    (center1751.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1751]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1751 : work1751.theta.ok = true ∧
    work1751.jac.invOK = true ∧ acceptsUnitSq work1751.out = true := by
  norm_num [work1751, contact1751, tau1751, center1751, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1751 : CellCertificate where
  tauBall := tau1751
  contactCenter := center1751
  contactBall := contact1751
  work := work1751
  center_sq := center_sq1751
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1751.1
  jac_ok := checks1751.2.1
  accepted := checks1751.2.2

def cells : List CellCertificate := [cell1744, cell1745, cell1746, cell1747, cell1748, cell1749, cell1750, cell1751]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0218
