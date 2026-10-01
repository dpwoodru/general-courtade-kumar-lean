import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1656 : RatBall :=
  ⟨⟨39/320, -111/320⟩, 3/640⟩
def center1656 : GaussianRat :=
  ⟨11957763/125000000, -15409367/62500000⟩
def contact1656 : RatBall := localContactBall tau1656 center1656
def work1656 : RoundedTauEval :=
  evalTau precision tau1656 contact1656 logTwoBall

theorem center_sq1656 : (center1656.re : ℝ)^2 +
    (center1656.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1656]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1656 : work1656.theta.ok = true ∧
    work1656.jac.invOK = true ∧ acceptsUnitSq work1656.out = true := by
  norm_num [work1656, contact1656, tau1656, center1656, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1656 : CellCertificate where
  tauBall := tau1656
  contactCenter := center1656
  contactBall := contact1656
  work := work1656
  center_sq := center_sq1656
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1656.1
  jac_ok := checks1656.2.1
  accepted := checks1656.2.2

def tau1657 : RatBall :=
  ⟨⟨37/320, -109/320⟩, 3/640⟩
def center1657 : GaussianRat :=
  ⟨45195779/500000000, -121096227/500000000⟩
def contact1657 : RatBall := localContactBall tau1657 center1657
def work1657 : RoundedTauEval :=
  evalTau precision tau1657 contact1657 logTwoBall

theorem center_sq1657 : (center1657.re : ℝ)^2 +
    (center1657.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1657]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1657 : work1657.theta.ok = true ∧
    work1657.jac.invOK = true ∧ acceptsUnitSq work1657.out = true := by
  norm_num [work1657, contact1657, tau1657, center1657, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1657 : CellCertificate where
  tauBall := tau1657
  contactCenter := center1657
  contactBall := contact1657
  work := work1657
  center_sq := center_sq1657
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1657.1
  jac_ok := checks1657.2.1
  accepted := checks1657.2.2

def tau1658 : RatBall :=
  ⟨⟨39/320, -109/320⟩, 3/640⟩
def center1658 : GaussianRat :=
  ⟨47597289/500000000, -241742219/1000000000⟩
def contact1658 : RatBall := localContactBall tau1658 center1658
def work1658 : RoundedTauEval :=
  evalTau precision tau1658 contact1658 logTwoBall

theorem center_sq1658 : (center1658.re : ℝ)^2 +
    (center1658.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1658]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1658 : work1658.theta.ok = true ∧
    work1658.jac.invOK = true ∧ acceptsUnitSq work1658.out = true := by
  norm_num [work1658, contact1658, tau1658, center1658, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1658 : CellCertificate where
  tauBall := tau1658
  contactCenter := center1658
  contactBall := contact1658
  work := work1658
  center_sq := center_sq1658
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1658.1
  jac_ok := checks1658.2.1
  accepted := checks1658.2.2

def tau1659 : RatBall :=
  ⟨⟨37/320, -107/320⟩, 3/640⟩
def center1659 : GaussianRat :=
  ⟨22489569/250000000, -47478823/200000000⟩
def contact1659 : RatBall := localContactBall tau1659 center1659
def work1659 : RoundedTauEval :=
  evalTau precision tau1659 contact1659 logTwoBall

theorem center_sq1659 : (center1659.re : ℝ)^2 +
    (center1659.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1659]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1659 : work1659.theta.ok = true ∧
    work1659.jac.invOK = true ∧ acceptsUnitSq work1659.out = true := by
  norm_num [work1659, contact1659, tau1659, center1659, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1659 : CellCertificate where
  tauBall := tau1659
  contactCenter := center1659
  contactBall := contact1659
  work := work1659
  center_sq := center_sq1659
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1659.1
  jac_ok := checks1659.2.1
  accepted := checks1659.2.2

def tau1660 : RatBall :=
  ⟨⟨39/320, -107/320⟩, 3/640⟩
def center1660 : GaussianRat :=
  ⟨23684951/250000000, -1184781/5000000⟩
def contact1660 : RatBall := localContactBall tau1660 center1660
def work1660 : RoundedTauEval :=
  evalTau precision tau1660 contact1660 logTwoBall

theorem center_sq1660 : (center1660.re : ℝ)^2 +
    (center1660.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1660]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1660 : work1660.theta.ok = true ∧
    work1660.jac.invOK = true ∧ acceptsUnitSq work1660.out = true := by
  norm_num [work1660, contact1660, tau1660, center1660, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1660 : CellCertificate where
  tauBall := tau1660
  contactCenter := center1660
  contactBall := contact1660
  work := work1660
  center_sq := center_sq1660
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1660.1
  jac_ok := checks1660.2.1
  accepted := checks1660.2.2

def tau1661 : RatBall :=
  ⟨⟨37/320, -21/64⟩, 3/640⟩
def center1661 : GaussianRat :=
  ⟨89536891/1000000000, -116308561/500000000⟩
def contact1661 : RatBall := localContactBall tau1661 center1661
def work1661 : RoundedTauEval :=
  evalTau precision tau1661 contact1661 logTwoBall

theorem center_sq1661 : (center1661.re : ℝ)^2 +
    (center1661.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1661]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1661 : work1661.theta.ok = true ∧
    work1661.jac.invOK = true ∧ acceptsUnitSq work1661.out = true := by
  norm_num [work1661, contact1661, tau1661, center1661, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1661 : CellCertificate where
  tauBall := tau1661
  contactCenter := center1661
  contactBall := contact1661
  work := work1661
  center_sq := center_sq1661
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1661.1
  jac_ok := checks1661.2.1
  accepted := checks1661.2.2

def tau1662 : RatBall :=
  ⟨⟨39/320, -21/64⟩, 3/640⟩
def center1662 : GaussianRat :=
  ⟨94297493/1000000000, -185753/800000⟩
def contact1662 : RatBall := localContactBall tau1662 center1662
def work1662 : RoundedTauEval :=
  evalTau precision tau1662 contact1662 logTwoBall

theorem center_sq1662 : (center1662.re : ℝ)^2 +
    (center1662.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1662]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1662 : work1662.theta.ok = true ∧
    work1662.jac.invOK = true ∧ acceptsUnitSq work1662.out = true := by
  norm_num [work1662, contact1662, tau1662, center1662, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1662 : CellCertificate where
  tauBall := tau1662
  contactCenter := center1662
  contactBall := contact1662
  work := work1662
  center_sq := center_sq1662
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1662.1
  jac_ok := checks1662.2.1
  accepted := checks1662.2.2

def tau1663 : RatBall :=
  ⟨⟨41/320, -111/320⟩, 3/640⟩
def center1663 : GaussianRat :=
  ⟨100474143/1000000000, -123032409/500000000⟩
def contact1663 : RatBall := localContactBall tau1663 center1663
def work1663 : RoundedTauEval :=
  evalTau precision tau1663 contact1663 logTwoBall

theorem center_sq1663 : (center1663.re : ℝ)^2 +
    (center1663.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1663]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1663 : work1663.theta.ok = true ∧
    work1663.jac.invOK = true ∧ acceptsUnitSq work1663.out = true := by
  norm_num [work1663, contact1663, tau1663, center1663, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1663 : CellCertificate where
  tauBall := tau1663
  contactCenter := center1663
  contactBall := contact1663
  work := work1663
  center_sq := center_sq1663
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1663.1
  jac_ok := checks1663.2.1
  accepted := checks1663.2.2

def cells : List CellCertificate := [cell1656, cell1657, cell1658, cell1659, cell1660, cell1661, cell1662, cell1663]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207
