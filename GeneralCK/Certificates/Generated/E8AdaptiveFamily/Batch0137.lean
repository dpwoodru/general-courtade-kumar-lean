import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1096 : RatBall :=
  ⟨⟨27/160, 41/160⟩, 3/320⟩
def center1096 : GaussianRat :=
  ⟨123867137/1000000000, 21999637/125000000⟩
def contact1096 : RatBall := localContactBall tau1096 center1096
def work1096 : RoundedTauEval :=
  evalTau precision tau1096 contact1096 logTwoBall

theorem center_sq1096 : (center1096.re : ℝ)^2 +
    (center1096.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1096]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1096 : work1096.theta.ok = true ∧
    work1096.jac.invOK = true ∧ acceptsUnitSq work1096.out = true := by
  norm_num [work1096, contact1096, tau1096, center1096, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1096 : CellCertificate where
  tauBall := tau1096
  contactCenter := center1096
  contactBall := contact1096
  work := work1096
  center_sq := center_sq1096
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1096.1
  jac_ok := checks1096.2.1
  accepted := checks1096.2.2

def tau1097 : RatBall :=
  ⟨⟨5/32, 43/160⟩, 3/320⟩
def center1097 : GaussianRat :=
  ⟨57855523/500000000, 185818573/1000000000⟩
def contact1097 : RatBall := localContactBall tau1097 center1097
def work1097 : RoundedTauEval :=
  evalTau precision tau1097 contact1097 logTwoBall

theorem center_sq1097 : (center1097.re : ℝ)^2 +
    (center1097.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1097]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1097 : work1097.theta.ok = true ∧
    work1097.jac.invOK = true ∧ acceptsUnitSq work1097.out = true := by
  norm_num [work1097, contact1097, tau1097, center1097, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1097 : CellCertificate where
  tauBall := tau1097
  contactCenter := center1097
  contactBall := contact1097
  work := work1097
  center_sq := center_sq1097
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1097.1
  jac_ok := checks1097.2.1
  accepted := checks1097.2.2

def tau1098 : RatBall :=
  ⟨⟨27/160, 43/160⟩, 3/320⟩
def center1098 : GaussianRat :=
  ⟨1948873/15625000, 92480083/500000000⟩
def contact1098 : RatBall := localContactBall tau1098 center1098
def work1098 : RoundedTauEval :=
  evalTau precision tau1098 contact1098 logTwoBall

theorem center_sq1098 : (center1098.re : ℝ)^2 +
    (center1098.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1098]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1098 : work1098.theta.ok = true ∧
    work1098.jac.invOK = true ∧ acceptsUnitSq work1098.out = true := by
  norm_num [work1098, contact1098, tau1098, center1098, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1098 : CellCertificate where
  tauBall := tau1098
  contactCenter := center1098
  contactBall := contact1098
  work := work1098
  center_sq := center_sq1098
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1098.1
  jac_ok := checks1098.2.1
  accepted := checks1098.2.2

def tau1099 : RatBall :=
  ⟨⟨29/160, 41/160⟩, 3/320⟩
def center1099 : GaussianRat :=
  ⟨132776829/1000000000, 35027183/200000000⟩
def contact1099 : RatBall := localContactBall tau1099 center1099
def work1099 : RoundedTauEval :=
  evalTau precision tau1099 contact1099 logTwoBall

theorem center_sq1099 : (center1099.re : ℝ)^2 +
    (center1099.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1099]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1099 : work1099.theta.ok = true ∧
    work1099.jac.invOK = true ∧ acceptsUnitSq work1099.out = true := by
  norm_num [work1099, contact1099, tau1099, center1099, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1099 : CellCertificate where
  tauBall := tau1099
  contactCenter := center1099
  contactBall := contact1099
  work := work1099
  center_sq := center_sq1099
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1099.1
  jac_ok := checks1099.2.1
  accepted := checks1099.2.2

def tau1100 : RatBall :=
  ⟨⟨31/160, 41/160⟩, 3/320⟩
def center1100 : GaussianRat :=
  ⟨8852011/62500000, 87111573/500000000⟩
def contact1100 : RatBall := localContactBall tau1100 center1100
def work1100 : RoundedTauEval :=
  evalTau precision tau1100 contact1100 logTwoBall

theorem center_sq1100 : (center1100.re : ℝ)^2 +
    (center1100.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1100]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1100 : work1100.theta.ok = true ∧
    work1100.jac.invOK = true ∧ acceptsUnitSq work1100.out = true := by
  norm_num [work1100, contact1100, tau1100, center1100, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1100 : CellCertificate where
  tauBall := tau1100
  contactCenter := center1100
  contactBall := contact1100
  work := work1100
  center_sq := center_sq1100
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1100.1
  jac_ok := checks1100.2.1
  accepted := checks1100.2.2

def tau1101 : RatBall :=
  ⟨⟨29/160, 43/160⟩, 3/320⟩
def center1101 : GaussianRat :=
  ⟨66845797/500000000, 18404523/100000000⟩
def contact1101 : RatBall := localContactBall tau1101 center1101
def work1101 : RoundedTauEval :=
  evalTau precision tau1101 contact1101 logTwoBall

theorem center_sq1101 : (center1101.re : ℝ)^2 +
    (center1101.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1101]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1101 : work1101.theta.ok = true ∧
    work1101.jac.invOK = true ∧ acceptsUnitSq work1101.out = true := by
  norm_num [work1101, contact1101, tau1101, center1101, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1101 : CellCertificate where
  tauBall := tau1101
  contactCenter := center1101
  contactBall := contact1101
  work := work1101
  center_sq := center_sq1101
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1101.1
  jac_ok := checks1101.2.1
  accepted := checks1101.2.2

def tau1102 : RatBall :=
  ⟨⟨31/160, 43/160⟩, 3/320⟩
def center1102 : GaussianRat :=
  ⟨71299541/500000000, 91537843/500000000⟩
def contact1102 : RatBall := localContactBall tau1102 center1102
def work1102 : RoundedTauEval :=
  evalTau precision tau1102 contact1102 logTwoBall

theorem center_sq1102 : (center1102.re : ℝ)^2 +
    (center1102.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1102]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1102 : work1102.theta.ok = true ∧
    work1102.jac.invOK = true ∧ acceptsUnitSq work1102.out = true := by
  norm_num [work1102, contact1102, tau1102, center1102, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1102 : CellCertificate where
  tauBall := tau1102
  contactCenter := center1102
  contactBall := contact1102
  work := work1102
  center_sq := center_sq1102
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1102.1
  jac_ok := checks1102.2.1
  accepted := checks1102.2.2

def tau1103 : RatBall :=
  ⟨⟨5/32, 9/32⟩, 3/320⟩
def center1103 : GaussianRat :=
  ⟨116565793/1000000000, 194890619/1000000000⟩
def contact1103 : RatBall := localContactBall tau1103 center1103
def work1103 : RoundedTauEval :=
  evalTau precision tau1103 contact1103 logTwoBall

theorem center_sq1103 : (center1103.re : ℝ)^2 +
    (center1103.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1103]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1103 : work1103.theta.ok = true ∧
    work1103.jac.invOK = true ∧ acceptsUnitSq work1103.out = true := by
  norm_num [work1103, contact1103, tau1103, center1103, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1103 : CellCertificate where
  tauBall := tau1103
  contactCenter := center1103
  contactBall := contact1103
  work := work1103
  center_sq := center_sq1103
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1103.1
  jac_ok := checks1103.2.1
  accepted := checks1103.2.2

def cells : List CellCertificate := [cell1096, cell1097, cell1098, cell1099, cell1100, cell1101, cell1102, cell1103]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137
