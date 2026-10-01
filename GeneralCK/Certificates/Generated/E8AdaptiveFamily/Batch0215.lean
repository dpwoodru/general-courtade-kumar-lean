import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1720 : RatBall :=
  ⟨⟨11/64, -101/320⟩, 3/640⟩
def center1720 : GaussianRat :=
  ⟨3268749/25000000, -54706193/250000000⟩
def contact1720 : RatBall := localContactBall tau1720 center1720
def work1720 : RoundedTauEval :=
  evalTau precision tau1720 contact1720 logTwoBall

theorem center_sq1720 : (center1720.re : ℝ)^2 +
    (center1720.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1720]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1720 : work1720.theta.ok = true ∧
    work1720.jac.invOK = true ∧ acceptsUnitSq work1720.out = true := by
  norm_num [work1720, contact1720, tau1720, center1720, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1720 : CellCertificate where
  tauBall := tau1720
  contactCenter := center1720
  contactBall := contact1720
  work := work1720
  center_sq := center_sq1720
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1720.1
  jac_ok := checks1720.2.1
  accepted := checks1720.2.2

def tau1721 : RatBall :=
  ⟨⟨57/320, -103/320⟩, 3/640⟩
def center1721 : GaussianRat :=
  ⟨135931497/1000000000, -55713833/250000000⟩
def contact1721 : RatBall := localContactBall tau1721 center1721
def work1721 : RoundedTauEval :=
  evalTau precision tau1721 contact1721 logTwoBall

theorem center_sq1721 : (center1721.re : ℝ)^2 +
    (center1721.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1721]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1721 : work1721.theta.ok = true ∧
    work1721.jac.invOK = true ∧ acceptsUnitSq work1721.out = true := by
  norm_num [work1721, contact1721, tau1721, center1721, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1721 : CellCertificate where
  tauBall := tau1721
  contactCenter := center1721
  contactBall := contact1721
  work := work1721
  center_sq := center_sq1721
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1721.1
  jac_ok := checks1721.2.1
  accepted := checks1721.2.2

def tau1722 : RatBall :=
  ⟨⟨59/320, -103/320⟩, 3/640⟩
def center1722 : GaussianRat :=
  ⟨140529903/1000000000, -222254637/1000000000⟩
def contact1722 : RatBall := localContactBall tau1722 center1722
def work1722 : RoundedTauEval :=
  evalTau precision tau1722 contact1722 logTwoBall

theorem center_sq1722 : (center1722.re : ℝ)^2 +
    (center1722.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1722]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1722 : work1722.theta.ok = true ∧
    work1722.jac.invOK = true ∧ acceptsUnitSq work1722.out = true := by
  norm_num [work1722, contact1722, tau1722, center1722, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1722 : CellCertificate where
  tauBall := tau1722
  contactCenter := center1722
  contactBall := contact1722
  work := work1722
  center_sq := center_sq1722
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1722.1
  jac_ok := checks1722.2.1
  accepted := checks1722.2.2

def tau1723 : RatBall :=
  ⟨⟨57/320, -101/320⟩, 3/640⟩
def center1723 : GaussianRat :=
  ⟨135347471/1000000000, -43651451/200000000⟩
def contact1723 : RatBall := localContactBall tau1723 center1723
def work1723 : RoundedTauEval :=
  evalTau precision tau1723 contact1723 logTwoBall

theorem center_sq1723 : (center1723.re : ℝ)^2 +
    (center1723.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1723]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1723 : work1723.theta.ok = true ∧
    work1723.jac.invOK = true ∧ acceptsUnitSq work1723.out = true := by
  norm_num [work1723, contact1723, tau1723, center1723, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1723 : CellCertificate where
  tauBall := tau1723
  contactCenter := center1723
  contactBall := contact1723
  work := work1723
  center_sq := center_sq1723
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1723.1
  jac_ok := checks1723.2.1
  accepted := checks1723.2.2

def tau1724 : RatBall :=
  ⟨⟨59/320, -101/320⟩, 3/640⟩
def center1724 : GaussianRat :=
  ⟨27985801/200000000, -54418229/250000000⟩
def contact1724 : RatBall := localContactBall tau1724 center1724
def work1724 : RoundedTauEval :=
  evalTau precision tau1724 contact1724 logTwoBall

theorem center_sq1724 : (center1724.re : ℝ)^2 +
    (center1724.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1724]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1724 : work1724.theta.ok = true ∧
    work1724.jac.invOK = true ∧ acceptsUnitSq work1724.out = true := by
  norm_num [work1724, contact1724, tau1724, center1724, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1724 : CellCertificate where
  tauBall := tau1724
  contactCenter := center1724
  contactBall := contact1724
  work := work1724
  center_sq := center_sq1724
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1724.1
  jac_ok := checks1724.2.1
  accepted := checks1724.2.2

def tau1725 : RatBall :=
  ⟨⟨61/320, -103/320⟩, 3/640⟩
def center1725 : GaussianRat :=
  ⟨5804463/40000000, -221637027/1000000000⟩
def contact1725 : RatBall := localContactBall tau1725 center1725
def work1725 : RoundedTauEval :=
  evalTau precision tau1725 contact1725 logTwoBall

theorem center_sq1725 : (center1725.re : ℝ)^2 +
    (center1725.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1725]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1725 : work1725.theta.ok = true ∧
    work1725.jac.invOK = true ∧ acceptsUnitSq work1725.out = true := by
  norm_num [work1725, contact1725, tau1725, center1725, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1725 : CellCertificate where
  tauBall := tau1725
  contactCenter := center1725
  contactBall := contact1725
  work := work1725
  center_sq := center_sq1725
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1725.1
  jac_ok := checks1725.2.1
  accepted := checks1725.2.2

def tau1726 : RatBall :=
  ⟨⟨63/320, -103/320⟩, 3/640⟩
def center1726 : GaussianRat :=
  ⟨74838049/500000000, -221002847/1000000000⟩
def contact1726 : RatBall := localContactBall tau1726 center1726
def work1726 : RoundedTauEval :=
  evalTau precision tau1726 contact1726 logTwoBall

theorem center_sq1726 : (center1726.re : ℝ)^2 +
    (center1726.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1726]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1726 : work1726.theta.ok = true ∧
    work1726.jac.invOK = true ∧ acceptsUnitSq work1726.out = true := by
  norm_num [work1726, contact1726, tau1726, center1726, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1726 : CellCertificate where
  tauBall := tau1726
  contactCenter := center1726
  contactBall := contact1726
  work := work1726
  center_sq := center_sq1726
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1726.1
  jac_ok := checks1726.2.1
  accepted := checks1726.2.2

def tau1727 : RatBall :=
  ⟨⟨61/320, -101/320⟩, 3/640⟩
def center1727 : GaussianRat :=
  ⟨7224707/50000000, -217072079/1000000000⟩
def contact1727 : RatBall := localContactBall tau1727 center1727
def work1727 : RoundedTauEval :=
  evalTau precision tau1727 contact1727 logTwoBall

theorem center_sq1727 : (center1727.re : ℝ)^2 +
    (center1727.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1727]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1727 : work1727.theta.ok = true ∧
    work1727.jac.invOK = true ∧ acceptsUnitSq work1727.out = true := by
  norm_num [work1727, contact1727, tau1727, center1727, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1727 : CellCertificate where
  tauBall := tau1727
  contactCenter := center1727
  contactBall := contact1727
  work := work1727
  center_sq := center_sq1727
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1727.1
  jac_ok := checks1727.2.1
  accepted := checks1727.2.2

def cells : List CellCertificate := [cell1720, cell1721, cell1722, cell1723, cell1724, cell1725, cell1726, cell1727]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215
