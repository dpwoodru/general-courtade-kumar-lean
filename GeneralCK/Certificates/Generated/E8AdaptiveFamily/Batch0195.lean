import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1560 : RatBall :=
  ⟨⟨1/64, -117/320⟩, 3/640⟩
def center1560 : GaussianRat :=
  ⟨1257211/100000000, -66538831/250000000⟩
def contact1560 : RatBall := localContactBall tau1560 center1560
def work1560 : RoundedTauEval :=
  evalTau precision tau1560 contact1560 logTwoBall

theorem center_sq1560 : (center1560.re : ℝ)^2 +
    (center1560.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1560]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1560 : work1560.theta.ok = true ∧
    work1560.jac.invOK = true ∧ acceptsUnitSq work1560.out = true := by
  norm_num [work1560, contact1560, tau1560, center1560, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1560 : CellCertificate where
  tauBall := tau1560
  contactCenter := center1560
  contactBall := contact1560
  work := work1560
  center_sq := center_sq1560
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1560.1
  jac_ok := checks1560.2.1
  accepted := checks1560.2.2

def tau1561 : RatBall :=
  ⟨⟨7/320, -117/320⟩, 3/640⟩
def center1561 : GaussianRat :=
  ⟨3519651/200000000, -8314767/31250000⟩
def contact1561 : RatBall := localContactBall tau1561 center1561
def work1561 : RoundedTauEval :=
  evalTau precision tau1561 contact1561 logTwoBall

theorem center_sq1561 : (center1561.re : ℝ)^2 +
    (center1561.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1561]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1561 : work1561.theta.ok = true ∧
    work1561.jac.invOK = true ∧ acceptsUnitSq work1561.out = true := by
  norm_num [work1561, contact1561, tau1561, center1561, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1561 : CellCertificate where
  tauBall := tau1561
  contactCenter := center1561
  contactBall := contact1561
  work := work1561
  center_sq := center_sq1561
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1561.1
  jac_ok := checks1561.2.1
  accepted := checks1561.2.2

def tau1562 : RatBall :=
  ⟨⟨1/64, -23/64⟩, 3/640⟩
def center1562 : GaussianRat :=
  ⟨1563007/125000000, -13057087/50000000⟩
def contact1562 : RatBall := localContactBall tau1562 center1562
def work1562 : RoundedTauEval :=
  evalTau precision tau1562 contact1562 logTwoBall

theorem center_sq1562 : (center1562.re : ℝ)^2 +
    (center1562.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1562]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1562 : work1562.theta.ok = true ∧
    work1562.jac.invOK = true ∧ acceptsUnitSq work1562.out = true := by
  norm_num [work1562, contact1562, tau1562, center1562, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1562 : CellCertificate where
  tauBall := tau1562
  contactCenter := center1562
  contactBall := contact1562
  work := work1562
  center_sq := center_sq1562
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1562.1
  jac_ok := checks1562.2.1
  accepted := checks1562.2.2

def tau1563 : RatBall :=
  ⟨⟨7/320, -23/64⟩, 3/640⟩
def center1563 : GaussianRat :=
  ⟨350061/20000000, -130530621/500000000⟩
def contact1563 : RatBall := localContactBall tau1563 center1563
def work1563 : RoundedTauEval :=
  evalTau precision tau1563 contact1563 logTwoBall

theorem center_sq1563 : (center1563.re : ℝ)^2 +
    (center1563.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1563]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1563 : work1563.theta.ok = true ∧
    work1563.jac.invOK = true ∧ acceptsUnitSq work1563.out = true := by
  norm_num [work1563, contact1563, tau1563, center1563, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1563 : CellCertificate where
  tauBall := tau1563
  contactCenter := center1563
  contactBall := contact1563
  work := work1563
  center_sq := center_sq1563
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1563.1
  jac_ok := checks1563.2.1
  accepted := checks1563.2.2

def tau1564 : RatBall :=
  ⟨⟨1/64, -113/320⟩, 3/640⟩
def center1564 : GaussianRat :=
  ⟨12437881/1000000000, -3201937/12500000⟩
def contact1564 : RatBall := localContactBall tau1564 center1564
def work1564 : RoundedTauEval :=
  evalTau precision tau1564 contact1564 logTwoBall

theorem center_sq1564 : (center1564.re : ℝ)^2 +
    (center1564.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1564]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1564 : work1564.theta.ok = true ∧
    work1564.jac.invOK = true ∧ acceptsUnitSq work1564.out = true := by
  norm_num [work1564, contact1564, tau1564, center1564, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1564 : CellCertificate where
  tauBall := tau1564
  contactCenter := center1564
  contactBall := contact1564
  work := work1564
  center_sq := center_sq1564
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1564.1
  jac_ok := checks1564.2.1
  accepted := checks1564.2.2

def tau1565 : RatBall :=
  ⟨⟨7/320, -113/320⟩, 3/640⟩
def center1565 : GaussianRat :=
  ⟨17410471/1000000000, -51215337/200000000⟩
def contact1565 : RatBall := localContactBall tau1565 center1565
def work1565 : RoundedTauEval :=
  evalTau precision tau1565 contact1565 logTwoBall

theorem center_sq1565 : (center1565.re : ℝ)^2 +
    (center1565.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1565]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1565 : work1565.theta.ok = true ∧
    work1565.jac.invOK = true ∧ acceptsUnitSq work1565.out = true := by
  norm_num [work1565, contact1565, tau1565, center1565, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1565 : CellCertificate where
  tauBall := tau1565
  contactCenter := center1565
  contactBall := contact1565
  work := work1565
  center_sq := center_sq1565
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1565.1
  jac_ok := checks1565.2.1
  accepted := checks1565.2.2

def tau1566 : RatBall :=
  ⟨⟨9/320, -119/320⟩, 3/640⟩
def center1566 : GaussianRat :=
  ⟨22747453/1000000000, -270997951/1000000000⟩
def contact1566 : RatBall := localContactBall tau1566 center1566
def work1566 : RoundedTauEval :=
  evalTau precision tau1566 contact1566 logTwoBall

theorem center_sq1566 : (center1566.re : ℝ)^2 +
    (center1566.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1566]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1566 : work1566.theta.ok = true ∧
    work1566.jac.invOK = true ∧ acceptsUnitSq work1566.out = true := by
  norm_num [work1566, contact1566, tau1566, center1566, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1566 : CellCertificate where
  tauBall := tau1566
  contactCenter := center1566
  contactBall := contact1566
  work := work1566
  center_sq := center_sq1566
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1566.1
  jac_ok := checks1566.2.1
  accepted := checks1566.2.2

def tau1567 : RatBall :=
  ⟨⟨11/320, -119/320⟩, 3/640⟩
def center1567 : GaussianRat :=
  ⟨27795199/1000000000, -135428181/500000000⟩
def contact1567 : RatBall := localContactBall tau1567 center1567
def work1567 : RoundedTauEval :=
  evalTau precision tau1567 contact1567 logTwoBall

theorem center_sq1567 : (center1567.re : ℝ)^2 +
    (center1567.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1567]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1567 : work1567.theta.ok = true ∧
    work1567.jac.invOK = true ∧ acceptsUnitSq work1567.out = true := by
  norm_num [work1567, contact1567, tau1567, center1567, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1567 : CellCertificate where
  tauBall := tau1567
  contactCenter := center1567
  contactBall := contact1567
  work := work1567
  center_sq := center_sq1567
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1567.1
  jac_ok := checks1567.2.1
  accepted := checks1567.2.2

def cells : List CellCertificate := [cell1560, cell1561, cell1562, cell1563, cell1564, cell1565, cell1566, cell1567]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195
