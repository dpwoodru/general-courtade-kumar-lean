import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1736 : RatBall :=
  ⟨⟨63/320, -97/320⟩, 3/640⟩
def center1736 : GaussianRat :=
  ⟨147826489/1000000000, -2592583/12500000⟩
def contact1736 : RatBall := localContactBall tau1736 center1736
def work1736 : RoundedTauEval :=
  evalTau precision tau1736 contact1736 logTwoBall

theorem center_sq1736 : (center1736.re : ℝ)^2 +
    (center1736.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1736]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1736 : work1736.theta.ok = true ∧
    work1736.jac.invOK = true ∧ acceptsUnitSq work1736.out = true := by
  norm_num [work1736, contact1736, tau1736, center1736, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1736 : CellCertificate where
  tauBall := tau1736
  contactCenter := center1736
  contactBall := contact1736
  work := work1736
  center_sq := center_sq1736
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1736.1
  jac_ok := checks1736.2.1
  accepted := checks1736.2.2

def tau1737 : RatBall :=
  ⟨⟨13/64, -107/320⟩, 3/640⟩
def center1737 : GaussianRat :=
  ⟨77788111/500000000, -229460827/1000000000⟩
def contact1737 : RatBall := localContactBall tau1737 center1737
def work1737 : RoundedTauEval :=
  evalTau precision tau1737 contact1737 logTwoBall

theorem center_sq1737 : (center1737.re : ℝ)^2 +
    (center1737.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1737]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1737 : work1737.theta.ok = true ∧
    work1737.jac.invOK = true ∧ acceptsUnitSq work1737.out = true := by
  norm_num [work1737, contact1737, tau1737, center1737, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1737 : CellCertificate where
  tauBall := tau1737
  contactCenter := center1737
  contactBall := contact1737
  work := work1737
  center_sq := center_sq1737
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1737.1
  jac_ok := checks1737.2.1
  accepted := checks1737.2.2

def tau1738 : RatBall :=
  ⟨⟨67/320, -107/320⟩, 3/640⟩
def center1738 : GaussianRat :=
  ⟨160137389/1000000000, -228757569/1000000000⟩
def contact1738 : RatBall := localContactBall tau1738 center1738
def work1738 : RoundedTauEval :=
  evalTau precision tau1738 contact1738 logTwoBall

theorem center_sq1738 : (center1738.re : ℝ)^2 +
    (center1738.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1738]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1738 : work1738.theta.ok = true ∧
    work1738.jac.invOK = true ∧ acceptsUnitSq work1738.out = true := by
  norm_num [work1738, contact1738, tau1738, center1738, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1738 : CellCertificate where
  tauBall := tau1738
  contactCenter := center1738
  contactBall := contact1738
  work := work1738
  center_sq := center_sq1738
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1738.1
  jac_ok := checks1738.2.1
  accepted := checks1738.2.2

def tau1739 : RatBall :=
  ⟨⟨13/64, -21/64⟩, 3/640⟩
def center1739 : GaussianRat :=
  ⟨30978099/200000000, -224898511/1000000000⟩
def contact1739 : RatBall := localContactBall tau1739 center1739
def work1739 : RoundedTauEval :=
  evalTau precision tau1739 contact1739 logTwoBall

theorem center_sq1739 : (center1739.re : ℝ)^2 +
    (center1739.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1739]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1739 : work1739.theta.ok = true ∧
    work1739.jac.invOK = true ∧ acceptsUnitSq work1739.out = true := by
  norm_num [work1739, contact1739, tau1739, center1739, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1739 : CellCertificate where
  tauBall := tau1739
  contactCenter := center1739
  contactBall := contact1739
  work := work1739
  center_sq := center_sq1739
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1739.1
  jac_ok := checks1739.2.1
  accepted := checks1739.2.2

def tau1740 : RatBall :=
  ⟨⟨67/320, -21/64⟩, 3/640⟩
def center1740 : GaussianRat :=
  ⟨79717703/500000000, -224213933/1000000000⟩
def contact1740 : RatBall := localContactBall tau1740 center1740
def work1740 : RoundedTauEval :=
  evalTau precision tau1740 contact1740 logTwoBall

theorem center_sq1740 : (center1740.re : ℝ)^2 +
    (center1740.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1740]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1740 : work1740.theta.ok = true ∧
    work1740.jac.invOK = true ∧ acceptsUnitSq work1740.out = true := by
  norm_num [work1740, contact1740, tau1740, center1740, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1740 : CellCertificate where
  tauBall := tau1740
  contactCenter := center1740
  contactBall := contact1740
  work := work1740
  center_sq := center_sq1740
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1740.1
  jac_ok := checks1740.2.1
  accepted := checks1740.2.2

def tau1741 : RatBall :=
  ⟨⟨69/320, -107/320⟩, 3/640⟩
def center1741 : GaussianRat :=
  ⟨20584937/125000000, -228038057/1000000000⟩
def contact1741 : RatBall := localContactBall tau1741 center1741
def work1741 : RoundedTauEval :=
  evalTau precision tau1741 contact1741 logTwoBall

theorem center_sq1741 : (center1741.re : ℝ)^2 +
    (center1741.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1741]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1741 : work1741.theta.ok = true ∧
    work1741.jac.invOK = true ∧ acceptsUnitSq work1741.out = true := by
  norm_num [work1741, contact1741, tau1741, center1741, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1741 : CellCertificate where
  tauBall := tau1741
  contactCenter := center1741
  contactBall := contact1741
  work := work1741
  center_sq := center_sq1741
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1741.1
  jac_ok := checks1741.2.1
  accepted := checks1741.2.2

def tau1742 : RatBall :=
  ⟨⟨69/320, -21/64⟩, 3/640⟩
def center1742 : GaussianRat :=
  ⟨81980819/500000000, -223513477/1000000000⟩
def contact1742 : RatBall := localContactBall tau1742 center1742
def work1742 : RoundedTauEval :=
  evalTau precision tau1742 contact1742 logTwoBall

theorem center_sq1742 : (center1742.re : ℝ)^2 +
    (center1742.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1742]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1742 : work1742.theta.ok = true ∧
    work1742.jac.invOK = true ∧ acceptsUnitSq work1742.out = true := by
  norm_num [work1742, contact1742, tau1742, center1742, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1742 : CellCertificate where
  tauBall := tau1742
  contactCenter := center1742
  contactBall := contact1742
  work := work1742
  center_sq := center_sq1742
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1742.1
  jac_ok := checks1742.2.1
  accepted := checks1742.2.2

def tau1743 : RatBall :=
  ⟨⟨71/320, -21/64⟩, 3/640⟩
def center1743 : GaussianRat :=
  ⟨168468823/1000000000, -55699379/250000000⟩
def contact1743 : RatBall := localContactBall tau1743 center1743
def work1743 : RoundedTauEval :=
  evalTau precision tau1743 contact1743 logTwoBall

theorem center_sq1743 : (center1743.re : ℝ)^2 +
    (center1743.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1743]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1743 : work1743.theta.ok = true ∧
    work1743.jac.invOK = true ∧ acceptsUnitSq work1743.out = true := by
  norm_num [work1743, contact1743, tau1743, center1743, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1743 : CellCertificate where
  tauBall := tau1743
  contactCenter := center1743
  contactBall := contact1743
  work := work1743
  center_sq := center_sq1743
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1743.1
  jac_ok := checks1743.2.1
  accepted := checks1743.2.2

def cells : List CellCertificate := [cell1736, cell1737, cell1738, cell1739, cell1740, cell1741, cell1742, cell1743]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217
