import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1072 : RatBall :=
  ⟨⟨27/160, 37/160⟩, 3/320⟩
def center1072 : GaussianRat :=
  ⟨122297939/1000000000, 158228017/1000000000⟩
def contact1072 : RatBall := localContactBall tau1072 center1072
def work1072 : RoundedTauEval :=
  evalTau precision tau1072 contact1072 logTwoBall

theorem center_sq1072 : (center1072.re : ℝ)^2 +
    (center1072.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1072]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1072 : work1072.theta.ok = true ∧
    work1072.jac.invOK = true ∧ acceptsUnitSq work1072.out = true := by
  norm_num [work1072, contact1072, tau1072, center1072, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1072 : CellCertificate where
  tauBall := tau1072
  contactCenter := center1072
  contactBall := contact1072
  work := work1072
  center_sq := center_sq1072
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1072.1
  jac_ok := checks1072.2.1
  accepted := checks1072.2.2

def tau1073 : RatBall :=
  ⟨⟨5/32, 39/160⟩, 3/320⟩
def center1073 : GaussianRat :=
  ⟨57074691/500000000, 83923163/500000000⟩
def contact1073 : RatBall := localContactBall tau1073 center1073
def work1073 : RoundedTauEval :=
  evalTau precision tau1073 contact1073 logTwoBall

theorem center_sq1073 : (center1073.re : ℝ)^2 +
    (center1073.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1073]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1073 : work1073.theta.ok = true ∧
    work1073.jac.invOK = true ∧ acceptsUnitSq work1073.out = true := by
  norm_num [work1073, contact1073, tau1073, center1073, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1073 : CellCertificate where
  tauBall := tau1073
  contactCenter := center1073
  contactBall := contact1073
  work := work1073
  center_sq := center_sq1073
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1073.1
  jac_ok := checks1073.2.1
  accepted := checks1073.2.2

def tau1074 : RatBall :=
  ⟨⟨27/160, 39/160⟩, 3/320⟩
def center1074 : GaussianRat :=
  ⟨123057717/1000000000, 167087407/1000000000⟩
def contact1074 : RatBall := localContactBall tau1074 center1074
def work1074 : RoundedTauEval :=
  evalTau precision tau1074 contact1074 logTwoBall

theorem center_sq1074 : (center1074.re : ℝ)^2 +
    (center1074.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1074]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1074 : work1074.theta.ok = true ∧
    work1074.jac.invOK = true ∧ acceptsUnitSq work1074.out = true := by
  norm_num [work1074, contact1074, tau1074, center1074, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1074 : CellCertificate where
  tauBall := tau1074
  contactCenter := center1074
  contactBall := contact1074
  work := work1074
  center_sq := center_sq1074
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1074.1
  jac_ok := checks1074.2.1
  accepted := checks1074.2.2

def tau1075 : RatBall :=
  ⟨⟨29/160, 37/160⟩, 3/320⟩
def center1075 : GaussianRat :=
  ⟨8194291/62500000, 7873457/50000000⟩
def contact1075 : RatBall := localContactBall tau1075 center1075
def work1075 : RoundedTauEval :=
  evalTau precision tau1075 contact1075 logTwoBall

theorem center_sq1075 : (center1075.re : ℝ)^2 +
    (center1075.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1075]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1075 : work1075.theta.ok = true ∧
    work1075.jac.invOK = true ∧ acceptsUnitSq work1075.out = true := by
  norm_num [work1075, contact1075, tau1075, center1075, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1075 : CellCertificate where
  tauBall := tau1075
  contactCenter := center1075
  contactBall := contact1075
  work := work1075
  center_sq := center_sq1075
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1075.1
  jac_ok := checks1075.2.1
  accepted := checks1075.2.2

def tau1076 : RatBall :=
  ⟨⟨31/160, 37/160⟩, 3/320⟩
def center1076 : GaussianRat :=
  ⟨139868391/1000000000, 78332251/500000000⟩
def contact1076 : RatBall := localContactBall tau1076 center1076
def work1076 : RoundedTauEval :=
  evalTau precision tau1076 contact1076 logTwoBall

theorem center_sq1076 : (center1076.re : ℝ)^2 +
    (center1076.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1076]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1076 : work1076.theta.ok = true ∧
    work1076.jac.invOK = true ∧ acceptsUnitSq work1076.out = true := by
  norm_num [work1076, contact1076, tau1076, center1076, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1076 : CellCertificate where
  tauBall := tau1076
  contactCenter := center1076
  contactBall := contact1076
  work := work1076
  center_sq := center_sq1076
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1076.1
  jac_ok := checks1076.2.1
  accepted := checks1076.2.2

def tau1077 : RatBall :=
  ⟨⟨29/160, 39/160⟩, 3/320⟩
def center1077 : GaussianRat :=
  ⟨131916433/1000000000, 83139101/500000000⟩
def contact1077 : RatBall := localContactBall tau1077 center1077
def work1077 : RoundedTauEval :=
  evalTau precision tau1077 contact1077 logTwoBall

theorem center_sq1077 : (center1077.re : ℝ)^2 +
    (center1077.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1077]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1077 : work1077.theta.ok = true ∧
    work1077.jac.invOK = true ∧ acceptsUnitSq work1077.out = true := by
  norm_num [work1077, contact1077, tau1077, center1077, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1077 : CellCertificate where
  tauBall := tau1077
  contactCenter := center1077
  contactBall := contact1077
  work := work1077
  center_sq := center_sq1077
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1077.1
  jac_ok := checks1077.2.1
  accepted := checks1077.2.2

def tau1078 : RatBall :=
  ⟨⟨31/160, 39/160⟩, 3/320⟩
def center1078 : GaussianRat :=
  ⟨2814451/20000000, 33084071/200000000⟩
def contact1078 : RatBall := localContactBall tau1078 center1078
def work1078 : RoundedTauEval :=
  evalTau precision tau1078 contact1078 logTwoBall

theorem center_sq1078 : (center1078.re : ℝ)^2 +
    (center1078.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1078]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1078 : work1078.theta.ok = true ∧
    work1078.jac.invOK = true ∧ acceptsUnitSq work1078.out = true := by
  norm_num [work1078, contact1078, tau1078, center1078, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1078 : CellCertificate where
  tauBall := tau1078
  contactCenter := center1078
  contactBall := contact1078
  work := work1078
  center_sq := center_sq1078
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1078.1
  jac_ok := checks1078.2.1
  accepted := checks1078.2.2

def tau1079 : RatBall :=
  ⟨⟨17/160, 41/160⟩, 3/320⟩
def center1079 : GaussianRat :=
  ⟨1572299/20000000, 179469913/1000000000⟩
def contact1079 : RatBall := localContactBall tau1079 center1079
def work1079 : RoundedTauEval :=
  evalTau precision tau1079 contact1079 logTwoBall

theorem center_sq1079 : (center1079.re : ℝ)^2 +
    (center1079.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1079]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1079 : work1079.theta.ok = true ∧
    work1079.jac.invOK = true ∧ acceptsUnitSq work1079.out = true := by
  norm_num [work1079, contact1079, tau1079, center1079, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1079 : CellCertificate where
  tauBall := tau1079
  contactCenter := center1079
  contactBall := contact1079
  work := work1079
  center_sq := center_sq1079
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1079.1
  jac_ok := checks1079.2.1
  accepted := checks1079.2.2

def cells : List CellCertificate := [cell1072, cell1073, cell1074, cell1075, cell1076, cell1077, cell1078, cell1079]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134
