import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1112 : RatBall :=
  ⟨⟨3/160, 49/160⟩, 3/320⟩
def center1112 : GaussianRat :=
  ⟨14395497/1000000000, 27438463/125000000⟩
def contact1112 : RatBall := localContactBall tau1112 center1112
def work1112 : RoundedTauEval :=
  evalTau precision tau1112 contact1112 logTwoBall

theorem center_sq1112 : (center1112.re : ℝ)^2 +
    (center1112.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1112]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1112 : work1112.theta.ok = true ∧
    work1112.jac.invOK = true ∧ acceptsUnitSq work1112.out = true := by
  norm_num [work1112, contact1112, tau1112, center1112, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1112 : CellCertificate where
  tauBall := tau1112
  contactCenter := center1112
  contactBall := contact1112
  work := work1112
  center_sq := center_sq1112
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1112.1
  jac_ok := checks1112.2.1
  accepted := checks1112.2.2

def tau1113 : RatBall :=
  ⟨⟨1/160, 51/160⟩, 3/320⟩
def center1113 : GaussianRat :=
  ⟨4842747/1000000000, 45846653/200000000⟩
def contact1113 : RatBall := localContactBall tau1113 center1113
def work1113 : RoundedTauEval :=
  evalTau precision tau1113 contact1113 logTwoBall

theorem center_sq1113 : (center1113.re : ℝ)^2 +
    (center1113.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1113]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1113 : work1113.theta.ok = true ∧
    work1113.jac.invOK = true ∧ acceptsUnitSq work1113.out = true := by
  norm_num [work1113, contact1113, tau1113, center1113, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1113 : CellCertificate where
  tauBall := tau1113
  contactCenter := center1113
  contactBall := contact1113
  work := work1113
  center_sq := center_sq1113
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1113.1
  jac_ok := checks1113.2.1
  accepted := checks1113.2.2

def tau1114 : RatBall :=
  ⟨⟨3/160, 51/160⟩, 3/320⟩
def center1114 : GaussianRat :=
  ⟨581027/40000000, 57285979/250000000⟩
def contact1114 : RatBall := localContactBall tau1114 center1114
def work1114 : RoundedTauEval :=
  evalTau precision tau1114 contact1114 logTwoBall

theorem center_sq1114 : (center1114.re : ℝ)^2 +
    (center1114.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1114]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1114 : work1114.theta.ok = true ∧
    work1114.jac.invOK = true ∧ acceptsUnitSq work1114.out = true := by
  norm_num [work1114, contact1114, tau1114, center1114, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1114 : CellCertificate where
  tauBall := tau1114
  contactCenter := center1114
  contactBall := contact1114
  work := work1114
  center_sq := center_sq1114
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1114.1
  jac_ok := checks1114.2.1
  accepted := checks1114.2.2

def tau1115 : RatBall :=
  ⟨⟨1/32, 49/160⟩, 3/320⟩
def center1115 : GaussianRat :=
  ⟨2398433/100000000, 219339251/1000000000⟩
def contact1115 : RatBall := localContactBall tau1115 center1115
def work1115 : RoundedTauEval :=
  evalTau precision tau1115 contact1115 logTwoBall

theorem center_sq1115 : (center1115.re : ℝ)^2 +
    (center1115.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1115]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1115 : work1115.theta.ok = true ∧
    work1115.jac.invOK = true ∧ acceptsUnitSq work1115.out = true := by
  norm_num [work1115, contact1115, tau1115, center1115, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1115 : CellCertificate where
  tauBall := tau1115
  contactCenter := center1115
  contactBall := contact1115
  work := work1115
  center_sq := center_sq1115
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1115.1
  jac_ok := checks1115.2.1
  accepted := checks1115.2.2

def tau1116 : RatBall :=
  ⟨⟨7/160, 49/160⟩, 3/320⟩
def center1116 : GaussianRat :=
  ⟨16780473/500000000, 219087113/1000000000⟩
def contact1116 : RatBall := localContactBall tau1116 center1116
def work1116 : RoundedTauEval :=
  evalTau precision tau1116 contact1116 logTwoBall

theorem center_sq1116 : (center1116.re : ℝ)^2 +
    (center1116.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1116]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1116 : work1116.theta.ok = true ∧
    work1116.jac.invOK = true ∧ acceptsUnitSq work1116.out = true := by
  norm_num [work1116, contact1116, tau1116, center1116, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1116 : CellCertificate where
  tauBall := tau1116
  contactCenter := center1116
  contactBall := contact1116
  work := work1116
  center_sq := center_sq1116
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1116.1
  jac_ok := checks1116.2.1
  accepted := checks1116.2.2

def tau1117 : RatBall :=
  ⟨⟨1/32, 51/160⟩, 3/320⟩
def center1117 : GaussianRat :=
  ⟨24200917/1000000000, 228965453/1000000000⟩
def contact1117 : RatBall := localContactBall tau1117 center1117
def work1117 : RoundedTauEval :=
  evalTau precision tau1117 contact1117 logTwoBall

theorem center_sq1117 : (center1117.re : ℝ)^2 +
    (center1117.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1117]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1117 : work1117.theta.ok = true ∧
    work1117.jac.invOK = true ∧ acceptsUnitSq work1117.out = true := by
  norm_num [work1117, contact1117, tau1117, center1117, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1117 : CellCertificate where
  tauBall := tau1117
  contactCenter := center1117
  contactBall := contact1117
  work := work1117
  center_sq := center_sq1117
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1117.1
  jac_ok := checks1117.2.1
  accepted := checks1117.2.2

def tau1118 : RatBall :=
  ⟨⟨7/160, 51/160⟩, 3/320⟩
def center1118 : GaussianRat :=
  ⟨1693169/50000000, 228698347/1000000000⟩
def contact1118 : RatBall := localContactBall tau1118 center1118
def work1118 : RoundedTauEval :=
  evalTau precision tau1118 contact1118 logTwoBall

theorem center_sq1118 : (center1118.re : ℝ)^2 +
    (center1118.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1118]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1118 : work1118.theta.ok = true ∧
    work1118.jac.invOK = true ∧ acceptsUnitSq work1118.out = true := by
  norm_num [work1118, contact1118, tau1118, center1118, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1118 : CellCertificate where
  tauBall := tau1118
  contactCenter := center1118
  contactBall := contact1118
  work := work1118
  center_sq := center_sq1118
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1118.1
  jac_ok := checks1118.2.1
  accepted := checks1118.2.2

def tau1119 : RatBall :=
  ⟨⟨1/160, 53/160⟩, 3/320⟩
def center1119 : GaussianRat :=
  ⟨611093/125000000, 238963881/1000000000⟩
def contact1119 : RatBall := localContactBall tau1119 center1119
def work1119 : RoundedTauEval :=
  evalTau precision tau1119 contact1119 logTwoBall

theorem center_sq1119 : (center1119.re : ℝ)^2 +
    (center1119.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1119]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1119 : work1119.theta.ok = true ∧
    work1119.jac.invOK = true ∧ acceptsUnitSq work1119.out = true := by
  norm_num [work1119, contact1119, tau1119, center1119, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1119 : CellCertificate where
  tauBall := tau1119
  contactCenter := center1119
  contactBall := contact1119
  work := work1119
  center_sq := center_sq1119
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1119.1
  jac_ok := checks1119.2.1
  accepted := checks1119.2.2

def cells : List CellCertificate := [cell1112, cell1113, cell1114, cell1115, cell1116, cell1117, cell1118, cell1119]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139
