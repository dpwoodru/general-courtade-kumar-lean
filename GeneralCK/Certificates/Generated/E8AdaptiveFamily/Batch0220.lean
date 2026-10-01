import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1760 : RatBall :=
  ⟨⟨71/320, -97/320⟩, 3/640⟩
def center1760 : GaussianRat :=
  ⟨41431439/250000000, -204924691/1000000000⟩
def contact1760 : RatBall := localContactBall tau1760 center1760
def work1760 : RoundedTauEval :=
  evalTau precision tau1760 contact1760 logTwoBall

theorem center_sq1760 : (center1760.re : ℝ)^2 +
    (center1760.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1760]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1760 : work1760.theta.ok = true ∧
    work1760.jac.invOK = true ∧ acceptsUnitSq work1760.out = true := by
  norm_num [work1760, contact1760, tau1760, center1760, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1760 : CellCertificate where
  tauBall := tau1760
  contactCenter := center1760
  contactBall := contact1760
  work := work1760
  center_sq := center_sq1760
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1760.1
  jac_ok := checks1760.2.1
  accepted := checks1760.2.2

def tau1761 : RatBall :=
  ⟨⟨73/320, -103/320⟩, 3/640⟩
def center1761 : GaussianRat :=
  ⟨34445579/200000000, -217595773/1000000000⟩
def contact1761 : RatBall := localContactBall tau1761 center1761
def work1761 : RoundedTauEval :=
  evalTau precision tau1761 contact1761 logTwoBall

theorem center_sq1761 : (center1761.re : ℝ)^2 +
    (center1761.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1761]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1761 : work1761.theta.ok = true ∧
    work1761.jac.invOK = true ∧ acceptsUnitSq work1761.out = true := by
  norm_num [work1761, contact1761, tau1761, center1761, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1761 : CellCertificate where
  tauBall := tau1761
  contactCenter := center1761
  contactBall := contact1761
  work := work1761
  center_sq := center_sq1761
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1761.1
  jac_ok := checks1761.2.1
  accepted := checks1761.2.2

def tau1762 : RatBall :=
  ⟨⟨15/64, -103/320⟩, 3/640⟩
def center1762 : GaussianRat :=
  ⟨44170389/250000000, -43373931/200000000⟩
def contact1762 : RatBall := localContactBall tau1762 center1762
def work1762 : RoundedTauEval :=
  evalTau precision tau1762 contact1762 logTwoBall

theorem center_sq1762 : (center1762.re : ℝ)^2 +
    (center1762.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1762]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1762 : work1762.theta.ok = true ∧
    work1762.jac.invOK = true ∧ acceptsUnitSq work1762.out = true := by
  norm_num [work1762, contact1762, tau1762, center1762, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1762 : CellCertificate where
  tauBall := tau1762
  contactCenter := center1762
  contactBall := contact1762
  work := work1762
  center_sq := center_sq1762
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1762.1
  jac_ok := checks1762.2.1
  accepted := checks1762.2.2

def tau1763 : RatBall :=
  ⟨⟨73/320, -101/320⟩, 3/640⟩
def center1763 : GaussianRat :=
  ⟨85759271/500000000, -26642441/125000000⟩
def contact1763 : RatBall := localContactBall tau1763 center1763
def work1763 : RoundedTauEval :=
  evalTau precision tau1763 contact1763 logTwoBall

theorem center_sq1763 : (center1763.re : ℝ)^2 +
    (center1763.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1763]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1763 : work1763.theta.ok = true ∧
    work1763.jac.invOK = true ∧ acceptsUnitSq work1763.out = true := by
  norm_num [work1763, contact1763, tau1763, center1763, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1763 : CellCertificate where
  tauBall := tau1763
  contactCenter := center1763
  contactBall := contact1763
  work := work1763
  center_sq := center_sq1763
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1763.1
  jac_ok := checks1763.2.1
  accepted := checks1763.2.2

def tau1764 : RatBall :=
  ⟨⟨15/64, -101/320⟩, 3/640⟩
def center1764 : GaussianRat :=
  ⟨21994767/125000000, -212432751/1000000000⟩
def contact1764 : RatBall := localContactBall tau1764 center1764
def work1764 : RoundedTauEval :=
  evalTau precision tau1764 contact1764 logTwoBall

theorem center_sq1764 : (center1764.re : ℝ)^2 +
    (center1764.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1764]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1764 : work1764.theta.ok = true ∧
    work1764.jac.invOK = true ∧ acceptsUnitSq work1764.out = true := by
  norm_num [work1764, contact1764, tau1764, center1764, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1764 : CellCertificate where
  tauBall := tau1764
  contactCenter := center1764
  contactBall := contact1764
  work := work1764
  center_sq := center_sq1764
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1764.1
  jac_ok := checks1764.2.1
  accepted := checks1764.2.2

def tau1765 : RatBall :=
  ⟨⟨77/320, -103/320⟩, 3/640⟩
def center1765 : GaussianRat :=
  ⟨36223107/200000000, -108064747/500000000⟩
def contact1765 : RatBall := localContactBall tau1765 center1765
def work1765 : RoundedTauEval :=
  evalTau precision tau1765 contact1765 logTwoBall

theorem center_sq1765 : (center1765.re : ℝ)^2 +
    (center1765.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1765]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1765 : work1765.theta.ok = true ∧
    work1765.jac.invOK = true ∧ acceptsUnitSq work1765.out = true := by
  norm_num [work1765, contact1765, tau1765, center1765, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1765 : CellCertificate where
  tauBall := tau1765
  contactCenter := center1765
  contactBall := contact1765
  work := work1765
  center_sq := center_sq1765
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1765.1
  jac_ok := checks1765.2.1
  accepted := checks1765.2.2

def tau1766 : RatBall :=
  ⟨⟨77/320, -101/320⟩, 3/640⟩
def center1766 : GaussianRat :=
  ⟨45094603/250000000, -105856123/500000000⟩
def contact1766 : RatBall := localContactBall tau1766 center1766
def work1766 : RoundedTauEval :=
  evalTau precision tau1766 contact1766 logTwoBall

theorem center_sq1766 : (center1766.re : ℝ)^2 +
    (center1766.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1766]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1766 : work1766.theta.ok = true ∧
    work1766.jac.invOK = true ∧ acceptsUnitSq work1766.out = true := by
  norm_num [work1766, contact1766, tau1766, center1766, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1766 : CellCertificate where
  tauBall := tau1766
  contactCenter := center1766
  contactBall := contact1766
  work := work1766
  center_sq := center_sq1766
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1766.1
  jac_ok := checks1766.2.1
  accepted := checks1766.2.2

def tau1767 : RatBall :=
  ⟨⟨79/320, -101/320⟩, 3/640⟩
def center1767 : GaussianRat :=
  ⟨92389531/500000000, -210978373/1000000000⟩
def contact1767 : RatBall := localContactBall tau1767 center1767
def work1767 : RoundedTauEval :=
  evalTau precision tau1767 contact1767 logTwoBall

theorem center_sq1767 : (center1767.re : ℝ)^2 +
    (center1767.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1767]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1767 : work1767.theta.ok = true ∧
    work1767.jac.invOK = true ∧ acceptsUnitSq work1767.out = true := by
  norm_num [work1767, contact1767, tau1767, center1767, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1767 : CellCertificate where
  tauBall := tau1767
  contactCenter := center1767
  contactBall := contact1767
  work := work1767
  center_sq := center_sq1767
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1767.1
  jac_ok := checks1767.2.1
  accepted := checks1767.2.2

def cells : List CellCertificate := [cell1760, cell1761, cell1762, cell1763, cell1764, cell1765, cell1766, cell1767]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220
