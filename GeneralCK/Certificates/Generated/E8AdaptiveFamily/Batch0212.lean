import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1696 : RatBall :=
  ⟨⟨11/64, -107/320⟩, 3/640⟩
def center1696 : GaussianRat :=
  ⟨66249189/500000000, -232719989/1000000000⟩
def contact1696 : RatBall := localContactBall tau1696 center1696
def work1696 : RoundedTauEval :=
  evalTau precision tau1696 contact1696 logTwoBall

theorem center_sq1696 : (center1696.re : ℝ)^2 +
    (center1696.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1696]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1696 : work1696.theta.ok = true ∧
    work1696.jac.invOK = true ∧ acceptsUnitSq work1696.out = true := by
  norm_num [work1696, contact1696, tau1696, center1696, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1696 : CellCertificate where
  tauBall := tau1696
  contactCenter := center1696
  contactBall := contact1696
  work := work1696
  center_sq := center_sq1696
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1696.1
  jac_ok := checks1696.2.1
  accepted := checks1696.2.2

def tau1697 : RatBall :=
  ⟨⟨53/320, -21/64⟩, 3/640⟩
def center1697 : GaussianRat :=
  ⟨127250921/1000000000, -228652029/1000000000⟩
def contact1697 : RatBall := localContactBall tau1697 center1697
def work1697 : RoundedTauEval :=
  evalTau precision tau1697 contact1697 logTwoBall

theorem center_sq1697 : (center1697.re : ℝ)^2 +
    (center1697.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1697]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1697 : work1697.theta.ok = true ∧
    work1697.jac.invOK = true ∧ acceptsUnitSq work1697.out = true := by
  norm_num [work1697, contact1697, tau1697, center1697, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1697 : CellCertificate where
  tauBall := tau1697
  contactCenter := center1697
  contactBall := contact1697
  work := work1697
  center_sq := center_sq1697
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1697.1
  jac_ok := checks1697.2.1
  accepted := checks1697.2.2

def tau1698 : RatBall :=
  ⟨⟨11/64, -21/64⟩, 3/640⟩
def center1698 : GaussianRat :=
  ⟨65949739/500000000, -57017591/250000000⟩
def contact1698 : RatBall := localContactBall tau1698 center1698
def work1698 : RoundedTauEval :=
  evalTau precision tau1698 contact1698 logTwoBall

theorem center_sq1698 : (center1698.re : ℝ)^2 +
    (center1698.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1698]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1698 : work1698.theta.ok = true ∧
    work1698.jac.invOK = true ∧ acceptsUnitSq work1698.out = true := by
  norm_num [work1698, contact1698, tau1698, center1698, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1698 : CellCertificate where
  tauBall := tau1698
  contactCenter := center1698
  contactBall := contact1698
  work := work1698
  center_sq := center_sq1698
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1698.1
  jac_ok := checks1698.2.1
  accepted := checks1698.2.2

def tau1699 : RatBall :=
  ⟨⟨57/320, -111/320⟩, 3/640⟩
def center1699 : GaussianRat :=
  ⟨138434183/1000000000, -120712289/500000000⟩
def contact1699 : RatBall := localContactBall tau1699 center1699
def work1699 : RoundedTauEval :=
  evalTau precision tau1699 contact1699 logTwoBall

theorem center_sq1699 : (center1699.re : ℝ)^2 +
    (center1699.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1699]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1699 : work1699.theta.ok = true ∧
    work1699.jac.invOK = true ∧ acceptsUnitSq work1699.out = true := by
  norm_num [work1699, contact1699, tau1699, center1699, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1699 : CellCertificate where
  tauBall := tau1699
  contactCenter := center1699
  contactBall := contact1699
  work := work1699
  center_sq := center_sq1699
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1699.1
  jac_ok := checks1699.2.1
  accepted := checks1699.2.2

def tau1700 : RatBall :=
  ⟨⟨59/320, -111/320⟩, 3/640⟩
def center1700 : GaussianRat :=
  ⟨143104409/1000000000, -240754941/1000000000⟩
def contact1700 : RatBall := localContactBall tau1700 center1700
def work1700 : RoundedTauEval :=
  evalTau precision tau1700 contact1700 logTwoBall

theorem center_sq1700 : (center1700.re : ℝ)^2 +
    (center1700.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1700]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1700 : work1700.theta.ok = true ∧
    work1700.jac.invOK = true ∧ acceptsUnitSq work1700.out = true := by
  norm_num [work1700, contact1700, tau1700, center1700, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1700 : CellCertificate where
  tauBall := tau1700
  contactCenter := center1700
  contactBall := contact1700
  work := work1700
  center_sq := center_sq1700
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1700.1
  jac_ok := checks1700.2.1
  accepted := checks1700.2.2

def tau1701 : RatBall :=
  ⟨⟨57/320, -109/320⟩, 3/640⟩
def center1701 : GaussianRat :=
  ⟨137782813/1000000000, -5918871/25000000⟩
def contact1701 : RatBall := localContactBall tau1701 center1701
def work1701 : RoundedTauEval :=
  evalTau precision tau1701 contact1701 logTwoBall

theorem center_sq1701 : (center1701.re : ℝ)^2 +
    (center1701.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1701]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1701 : work1701.theta.ok = true ∧
    work1701.jac.invOK = true ∧ acceptsUnitSq work1701.out = true := by
  norm_num [work1701, contact1701, tau1701, center1701, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1701 : CellCertificate where
  tauBall := tau1701
  contactCenter := center1701
  contactBall := contact1701
  work := work1701
  center_sq := center_sq1701
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1701.1
  jac_ok := checks1701.2.1
  accepted := checks1701.2.2

def tau1702 : RatBall :=
  ⟨⟨59/320, -109/320⟩, 3/640⟩
def center1702 : GaussianRat :=
  ⟨71217211/500000000, -236102993/1000000000⟩
def contact1702 : RatBall := localContactBall tau1702 center1702
def work1702 : RoundedTauEval :=
  evalTau precision tau1702 contact1702 logTwoBall

theorem center_sq1702 : (center1702.re : ℝ)^2 +
    (center1702.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1702]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1702 : work1702.theta.ok = true ∧
    work1702.jac.invOK = true ∧ acceptsUnitSq work1702.out = true := by
  norm_num [work1702, contact1702, tau1702, center1702, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1702 : CellCertificate where
  tauBall := tau1702
  contactCenter := center1702
  contactBall := contact1702
  work := work1702
  center_sq := center_sq1702
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1702.1
  jac_ok := checks1702.2.1
  accepted := checks1702.2.2

def tau1703 : RatBall :=
  ⟨⟨61/320, -109/320⟩, 3/640⟩
def center1703 : GaussianRat :=
  ⟨147068213/1000000000, -14714559/62500000⟩
def contact1703 : RatBall := localContactBall tau1703 center1703
def work1703 : RoundedTauEval :=
  evalTau precision tau1703 contact1703 logTwoBall

theorem center_sq1703 : (center1703.re : ℝ)^2 +
    (center1703.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1703]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1703 : work1703.theta.ok = true ∧
    work1703.jac.invOK = true ∧ acceptsUnitSq work1703.out = true := by
  norm_num [work1703, contact1703, tau1703, center1703, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1703 : CellCertificate where
  tauBall := tau1703
  contactCenter := center1703
  contactBall := contact1703
  work := work1703
  center_sq := center_sq1703
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1703.1
  jac_ok := checks1703.2.1
  accepted := checks1703.2.2

def cells : List CellCertificate := [cell1696, cell1697, cell1698, cell1699, cell1700, cell1701, cell1702, cell1703]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212
