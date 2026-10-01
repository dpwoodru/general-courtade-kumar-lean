import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0222

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1776 : RatBall :=
  ⟨⟨81/320, -99/320⟩, 3/640⟩
def center1776 : GaussianRat :=
  ⟨47104143/250000000, -25733387/125000000⟩
def contact1776 : RatBall := localContactBall tau1776 center1776
def work1776 : RoundedTauEval :=
  evalTau precision tau1776 contact1776 logTwoBall

theorem center_sq1776 : (center1776.re : ℝ)^2 +
    (center1776.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1776]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1776 : work1776.theta.ok = true ∧
    work1776.jac.invOK = true ∧ acceptsUnitSq work1776.out = true := by
  norm_num [work1776, contact1776, tau1776, center1776, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1776 : CellCertificate where
  tauBall := tau1776
  contactCenter := center1776
  contactBall := contact1776
  work := work1776
  center_sq := center_sq1776
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1776.1
  jac_ok := checks1776.2.1
  accepted := checks1776.2.2

def tau1777 : RatBall :=
  ⟨⟨83/320, -99/320⟩, 3/640⟩
def center1777 : GaussianRat :=
  ⟨19276477/100000000, -205127733/1000000000⟩
def contact1777 : RatBall := localContactBall tau1777 center1777
def work1777 : RoundedTauEval :=
  evalTau precision tau1777 contact1777 logTwoBall

theorem center_sq1777 : (center1777.re : ℝ)^2 +
    (center1777.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1777]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1777 : work1777.theta.ok = true ∧
    work1777.jac.invOK = true ∧ acceptsUnitSq work1777.out = true := by
  norm_num [work1777, contact1777, tau1777, center1777, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1777 : CellCertificate where
  tauBall := tau1777
  contactCenter := center1777
  contactBall := contact1777
  work := work1777
  center_sq := center_sq1777
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1777.1
  jac_ok := checks1777.2.1
  accepted := checks1777.2.2

def tau1778 : RatBall :=
  ⟨⟨81/320, -97/320⟩, 3/640⟩
def center1778 : GaussianRat :=
  ⟨469233/2500000, -201515067/1000000000⟩
def contact1778 : RatBall := localContactBall tau1778 center1778
def work1778 : RoundedTauEval :=
  evalTau precision tau1778 contact1778 logTwoBall

theorem center_sq1778 : (center1778.re : ℝ)^2 +
    (center1778.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1778]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1778 : work1778.theta.ok = true ∧
    work1778.jac.invOK = true ∧ acceptsUnitSq work1778.out = true := by
  norm_num [work1778, contact1778, tau1778, center1778, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1778 : CellCertificate where
  tauBall := tau1778
  contactCenter := center1778
  contactBall := contact1778
  work := work1778
  center_sq := center_sq1778
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1778.1
  jac_ok := checks1778.2.1
  accepted := checks1778.2.2

def tau1779 : RatBall :=
  ⟨⟨83/320, -97/320⟩, 3/640⟩
def center1779 : GaussianRat :=
  ⟨9601467/50000000, -100397757/500000000⟩
def contact1779 : RatBall := localContactBall tau1779 center1779
def work1779 : RoundedTauEval :=
  evalTau precision tau1779 contact1779 logTwoBall

theorem center_sq1779 : (center1779.re : ℝ)^2 +
    (center1779.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1779]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1779 : work1779.theta.ok = true ∧
    work1779.jac.invOK = true ∧ acceptsUnitSq work1779.out = true := by
  norm_num [work1779, contact1779, tau1779, center1779, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1779 : CellCertificate where
  tauBall := tau1779
  contactCenter := center1779
  contactBall := contact1779
  work := work1779
  center_sq := center_sq1779
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1779.1
  jac_ok := checks1779.2.1
  accepted := checks1779.2.2

def tau1780 : RatBall :=
  ⟨⟨17/64, -97/320⟩, 3/640⟩
def center1780 : GaussianRat :=
  ⟨49086427/250000000, -200064207/1000000000⟩
def contact1780 : RatBall := localContactBall tau1780 center1780
def work1780 : RoundedTauEval :=
  evalTau precision tau1780 contact1780 logTwoBall

theorem center_sq1780 : (center1780.re : ℝ)^2 +
    (center1780.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1780]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1780 : work1780.theta.ok = true ∧
    work1780.jac.invOK = true ∧ acceptsUnitSq work1780.out = true := by
  norm_num [work1780, contact1780, tau1780, center1780, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1780 : CellCertificate where
  tauBall := tau1780
  contactCenter := center1780
  contactBall := contact1780
  work := work1780
  center_sq := center_sq1780
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1780.1
  jac_ok := checks1780.2.1
  accepted := checks1780.2.2

def tau1781 : RatBall :=
  ⟨⟨13/64, -19/64⟩, 3/640⟩
def center1781 : GaussianRat :=
  ⟨30345869/200000000, -40464617/200000000⟩
def contact1781 : RatBall := localContactBall tau1781 center1781
def work1781 : RoundedTauEval :=
  evalTau precision tau1781 contact1781 logTwoBall

theorem center_sq1781 : (center1781.re : ℝ)^2 +
    (center1781.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1781]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1781 : work1781.theta.ok = true ∧
    work1781.jac.invOK = true ∧ acceptsUnitSq work1781.out = true := by
  norm_num [work1781, contact1781, tau1781, center1781, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1781 : CellCertificate where
  tauBall := tau1781
  contactCenter := center1781
  contactBall := contact1781
  work := work1781
  center_sq := center_sq1781
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1781.1
  jac_ok := checks1781.2.1
  accepted := checks1781.2.2

def tau1782 : RatBall :=
  ⟨⟨67/320, -19/64⟩, 3/640⟩
def center1782 : GaussianRat :=
  ⟨78099293/500000000, -100863299/500000000⟩
def contact1782 : RatBall := localContactBall tau1782 center1782
def work1782 : RoundedTauEval :=
  evalTau precision tau1782 contact1782 logTwoBall

theorem center_sq1782 : (center1782.re : ℝ)^2 +
    (center1782.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1782]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1782 : work1782.theta.ok = true ∧
    work1782.jac.invOK = true ∧ acceptsUnitSq work1782.out = true := by
  norm_num [work1782, contact1782, tau1782, center1782, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1782 : CellCertificate where
  tauBall := tau1782
  contactCenter := center1782
  contactBall := contact1782
  work := work1782
  center_sq := center_sq1782
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1782.1
  jac_ok := checks1782.2.1
  accepted := checks1782.2.2

def tau1783 : RatBall :=
  ⟨⟨13/64, -93/320⟩, 3/640⟩
def center1783 : GaussianRat :=
  ⟨151148249/1000000000, -98926301/500000000⟩
def contact1783 : RatBall := localContactBall tau1783 center1783
def work1783 : RoundedTauEval :=
  evalTau precision tau1783 contact1783 logTwoBall

theorem center_sq1783 : (center1783.re : ℝ)^2 +
    (center1783.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1783]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1783 : work1783.theta.ok = true ∧
    work1783.jac.invOK = true ∧ acceptsUnitSq work1783.out = true := by
  norm_num [work1783, contact1783, tau1783, center1783, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1783 : CellCertificate where
  tauBall := tau1783
  contactCenter := center1783
  contactBall := contact1783
  work := work1783
  center_sq := center_sq1783
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1783.1
  jac_ok := checks1783.2.1
  accepted := checks1783.2.2

def cells : List CellCertificate := [cell1776, cell1777, cell1778, cell1779, cell1780, cell1781, cell1782, cell1783]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0222
