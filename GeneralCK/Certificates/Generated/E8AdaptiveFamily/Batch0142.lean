import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1136 : RatBall :=
  ⟨⟨11/160, 53/160⟩, 3/320⟩
def center1136 : GaussianRat :=
  ⟨53629143/1000000000, 118776899/500000000⟩
def contact1136 : RatBall := localContactBall tau1136 center1136
def work1136 : RoundedTauEval :=
  evalTau precision tau1136 contact1136 logTwoBall

theorem center_sq1136 : (center1136.re : ℝ)^2 +
    (center1136.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1136]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1136 : work1136.theta.ok = true ∧
    work1136.jac.invOK = true ∧ acceptsUnitSq work1136.out = true := by
  norm_num [work1136, contact1136, tau1136, center1136, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1136 : CellCertificate where
  tauBall := tau1136
  contactCenter := center1136
  contactBall := contact1136
  work := work1136
  center_sq := center_sq1136
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1136.1
  jac_ok := checks1136.2.1
  accepted := checks1136.2.2

def tau1137 : RatBall :=
  ⟨⟨9/160, 11/32⟩, 3/320⟩
def center1137 : GaussianRat :=
  ⟨44352537/1000000000, 61948059/250000000⟩
def contact1137 : RatBall := localContactBall tau1137 center1137
def work1137 : RoundedTauEval :=
  evalTau precision tau1137 contact1137 logTwoBall

theorem center_sq1137 : (center1137.re : ℝ)^2 +
    (center1137.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1137]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1137 : work1137.theta.ok = true ∧
    work1137.jac.invOK = true ∧ acceptsUnitSq work1137.out = true := by
  norm_num [work1137, contact1137, tau1137, center1137, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1137 : CellCertificate where
  tauBall := tau1137
  contactCenter := center1137
  contactBall := contact1137
  work := work1137
  center_sq := center_sq1137
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1137.1
  jac_ok := checks1137.2.1
  accepted := checks1137.2.2

def tau1138 : RatBall :=
  ⟨⟨13/160, 53/160⟩, 3/320⟩
def center1138 : GaussianRat :=
  ⟨63310961/1000000000, 236995059/1000000000⟩
def contact1138 : RatBall := localContactBall tau1138 center1138
def work1138 : RoundedTauEval :=
  evalTau precision tau1138 contact1138 logTwoBall

theorem center_sq1138 : (center1138.re : ℝ)^2 +
    (center1138.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1138]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1138 : work1138.theta.ok = true ∧
    work1138.jac.invOK = true ∧ acceptsUnitSq work1138.out = true := by
  norm_num [work1138, contact1138, tau1138, center1138, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1138 : CellCertificate where
  tauBall := tau1138
  contactCenter := center1138
  contactBall := contact1138
  work := work1138
  center_sq := center_sq1138
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1138.1
  jac_ok := checks1138.2.1
  accepted := checks1138.2.2

def tau1139 : RatBall :=
  ⟨⟨3/32, 53/160⟩, 3/320⟩
def center1139 : GaussianRat :=
  ⟨72958787/1000000000, 47269393/200000000⟩
def contact1139 : RatBall := localContactBall tau1139 center1139
def work1139 : RoundedTauEval :=
  evalTau precision tau1139 contact1139 logTwoBall

theorem center_sq1139 : (center1139.re : ℝ)^2 +
    (center1139.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1139]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1139 : work1139.theta.ok = true ∧
    work1139.jac.invOK = true ∧ acceptsUnitSq work1139.out = true := by
  norm_num [work1139, contact1139, tau1139, center1139, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1139 : CellCertificate where
  tauBall := tau1139
  contactCenter := center1139
  contactBall := contact1139
  work := work1139
  center_sq := center_sq1139
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1139.1
  jac_ok := checks1139.2.1
  accepted := checks1139.2.2

def tau1140 : RatBall :=
  ⟨⟨1/160, 57/160⟩, 3/320⟩
def center1140 : GaussianRat :=
  ⟨311809/62500000, 5174291/20000000⟩
def contact1140 : RatBall := localContactBall tau1140 center1140
def work1140 : RoundedTauEval :=
  evalTau precision tau1140 contact1140 logTwoBall

theorem center_sq1140 : (center1140.re : ℝ)^2 +
    (center1140.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1140]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1140 : work1140.theta.ok = true ∧
    work1140.jac.invOK = true ∧ acceptsUnitSq work1140.out = true := by
  norm_num [work1140, contact1140, tau1140, center1140, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1140 : CellCertificate where
  tauBall := tau1140
  contactCenter := center1140
  contactBall := contact1140
  work := work1140
  center_sq := center_sq1140
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1140.1
  jac_ok := checks1140.2.1
  accepted := checks1140.2.2

def tau1141 : RatBall :=
  ⟨⟨17/160, 49/160⟩, 3/320⟩
def center1141 : GaussianRat :=
  ⟨5068403/62500000, 846097/3906250⟩
def contact1141 : RatBall := localContactBall tau1141 center1141
def work1141 : RoundedTauEval :=
  evalTau precision tau1141 contact1141 logTwoBall

theorem center_sq1141 : (center1141.re : ℝ)^2 +
    (center1141.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1141]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1141 : work1141.theta.ok = true ∧
    work1141.jac.invOK = true ∧ acceptsUnitSq work1141.out = true := by
  norm_num [work1141, contact1141, tau1141, center1141, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1141 : CellCertificate where
  tauBall := tau1141
  contactCenter := center1141
  contactBall := contact1141
  work := work1141
  center_sq := center_sq1141
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1141.1
  jac_ok := checks1141.2.1
  accepted := checks1141.2.2

def tau1142 : RatBall :=
  ⟨⟨19/160, 49/160⟩, 3/320⟩
def center1142 : GaussianRat :=
  ⟨90499187/1000000000, 215867147/1000000000⟩
def contact1142 : RatBall := localContactBall tau1142 center1142
def work1142 : RoundedTauEval :=
  evalTau precision tau1142 contact1142 logTwoBall

theorem center_sq1142 : (center1142.re : ℝ)^2 +
    (center1142.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1142]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1142 : work1142.theta.ok = true ∧
    work1142.jac.invOK = true ∧ acceptsUnitSq work1142.out = true := by
  norm_num [work1142, contact1142, tau1142, center1142, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1142 : CellCertificate where
  tauBall := tau1142
  contactCenter := center1142
  contactBall := contact1142
  work := work1142
  center_sq := center_sq1142
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1142.1
  jac_ok := checks1142.2.1
  accepted := checks1142.2.2

def tau1143 : RatBall :=
  ⟨⟨17/160, 51/160⟩, 3/320⟩
def center1143 : GaussianRat :=
  ⟨40905123/500000000, 113032697/500000000⟩
def contact1143 : RatBall := localContactBall tau1143 center1143
def work1143 : RoundedTauEval :=
  evalTau precision tau1143 contact1143 logTwoBall

theorem center_sq1143 : (center1143.re : ℝ)^2 +
    (center1143.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1143]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1143 : work1143.theta.ok = true ∧
    work1143.jac.invOK = true ∧ acceptsUnitSq work1143.out = true := by
  norm_num [work1143, contact1143, tau1143, center1143, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1143 : CellCertificate where
  tauBall := tau1143
  contactCenter := center1143
  contactBall := contact1143
  work := work1143
  center_sq := center_sq1143
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1143.1
  jac_ok := checks1143.2.1
  accepted := checks1143.2.2

def cells : List CellCertificate := [cell1136, cell1137, cell1138, cell1139, cell1140, cell1141, cell1142, cell1143]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142
