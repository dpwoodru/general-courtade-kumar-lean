import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0146

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1168 : RatBall :=
  ⟨⟨43/160, 33/160⟩, 3/320⟩
def center1168 : GaussianRat :=
  ⟨189219451/1000000000, 67150009/500000000⟩
def contact1168 : RatBall := localContactBall tau1168 center1168
def work1168 : RoundedTauEval :=
  evalTau precision tau1168 contact1168 logTwoBall

theorem center_sq1168 : (center1168.re : ℝ)^2 +
    (center1168.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1168]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1168 : work1168.theta.ok = true ∧
    work1168.jac.invOK = true ∧ acceptsUnitSq work1168.out = true := by
  norm_num [work1168, contact1168, tau1168, center1168, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1168 : CellCertificate where
  tauBall := tau1168
  contactCenter := center1168
  contactBall := contact1168
  work := work1168
  center_sq := center_sq1168
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1168.1
  jac_ok := checks1168.2.1
  accepted := checks1168.2.2

def tau1169 : RatBall :=
  ⟨⟨41/160, 7/32⟩, 3/320⟩
def center1169 : GaussianRat :=
  ⟨90907579/500000000, 143596387/1000000000⟩
def contact1169 : RatBall := localContactBall tau1169 center1169
def work1169 : RoundedTauEval :=
  evalTau precision tau1169 contact1169 logTwoBall

theorem center_sq1169 : (center1169.re : ℝ)^2 +
    (center1169.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1169]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1169 : work1169.theta.ok = true ∧
    work1169.jac.invOK = true ∧ acceptsUnitSq work1169.out = true := by
  norm_num [work1169, contact1169, tau1169, center1169, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1169 : CellCertificate where
  tauBall := tau1169
  contactCenter := center1169
  contactBall := contact1169
  work := work1169
  center_sq := center_sq1169
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1169.1
  jac_ok := checks1169.2.1
  accepted := checks1169.2.2

def tau1170 : RatBall :=
  ⟨⟨43/160, 7/32⟩, 3/320⟩
def center1170 : GaussianRat :=
  ⟨9509069/50000000, 71308977/500000000⟩
def contact1170 : RatBall := localContactBall tau1170 center1170
def work1170 : RoundedTauEval :=
  evalTau precision tau1170 contact1170 logTwoBall

theorem center_sq1170 : (center1170.re : ℝ)^2 +
    (center1170.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1170]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1170 : work1170.theta.ok = true ∧
    work1170.jac.invOK = true ∧ acceptsUnitSq work1170.out = true := by
  norm_num [work1170, contact1170, tau1170, center1170, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1170 : CellCertificate where
  tauBall := tau1170
  contactCenter := center1170
  contactBall := contact1170
  work := work1170
  center_sq := center_sq1170
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1170.1
  jac_ok := checks1170.2.1
  accepted := checks1170.2.2

def tau1171 : RatBall :=
  ⟨⟨9/32, 33/160⟩, 3/320⟩
def center1171 : GaussianRat :=
  ⟨197489591/1000000000, 66677907/500000000⟩
def contact1171 : RatBall := localContactBall tau1171 center1171
def work1171 : RoundedTauEval :=
  evalTau precision tau1171 contact1171 logTwoBall

theorem center_sq1171 : (center1171.re : ℝ)^2 +
    (center1171.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1171]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1171 : work1171.theta.ok = true ∧
    work1171.jac.invOK = true ∧ acceptsUnitSq work1171.out = true := by
  norm_num [work1171, contact1171, tau1171, center1171, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1171 : CellCertificate where
  tauBall := tau1171
  contactCenter := center1171
  contactBall := contact1171
  work := work1171
  center_sq := center_sq1171
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1171.1
  jac_ok := checks1171.2.1
  accepted := checks1171.2.2

def tau1172 : RatBall :=
  ⟨⟨47/160, 33/160⟩, 3/320⟩
def center1172 : GaussianRat :=
  ⟨205693537/1000000000, 132383201/1000000000⟩
def contact1172 : RatBall := localContactBall tau1172 center1172
def work1172 : RoundedTauEval :=
  evalTau precision tau1172 contact1172 logTwoBall

theorem center_sq1172 : (center1172.re : ℝ)^2 +
    (center1172.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1172]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1172 : work1172.theta.ok = true ∧
    work1172.jac.invOK = true ∧ acceptsUnitSq work1172.out = true := by
  norm_num [work1172, contact1172, tau1172, center1172, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1172 : CellCertificate where
  tauBall := tau1172
  contactCenter := center1172
  contactBall := contact1172
  work := work1172
  center_sq := center_sq1172
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1172.1
  jac_ok := checks1172.2.1
  accepted := checks1172.2.2

def tau1173 : RatBall :=
  ⟨⟨9/32, 7/32⟩, 3/320⟩
def center1173 : GaussianRat :=
  ⟨49620407/250000000, 141607653/1000000000⟩
def contact1173 : RatBall := localContactBall tau1173 center1173
def work1173 : RoundedTauEval :=
  evalTau precision tau1173 contact1173 logTwoBall

theorem center_sq1173 : (center1173.re : ℝ)^2 +
    (center1173.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1173]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1173 : work1173.theta.ok = true ∧
    work1173.jac.invOK = true ∧ acceptsUnitSq work1173.out = true := by
  norm_num [work1173, contact1173, tau1173, center1173, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1173 : CellCertificate where
  tauBall := tau1173
  contactCenter := center1173
  contactBall := contact1173
  work := work1173
  center_sq := center_sq1173
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1173.1
  jac_ok := checks1173.2.1
  accepted := checks1173.2.2

def tau1174 : RatBall :=
  ⟨⟨47/160, 7/32⟩, 3/320⟩
def center1174 : GaussianRat :=
  ⟨206714057/1000000000, 70283583/500000000⟩
def contact1174 : RatBall := localContactBall tau1174 center1174
def work1174 : RoundedTauEval :=
  evalTau precision tau1174 contact1174 logTwoBall

theorem center_sq1174 : (center1174.re : ℝ)^2 +
    (center1174.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1174]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1174 : work1174.theta.ok = true ∧
    work1174.jac.invOK = true ∧ acceptsUnitSq work1174.out = true := by
  norm_num [work1174, contact1174, tau1174, center1174, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1174 : CellCertificate where
  tauBall := tau1174
  contactCenter := center1174
  contactBall := contact1174
  work := work1174
  center_sq := center_sq1174
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1174.1
  jac_ok := checks1174.2.1
  accepted := checks1174.2.2

def tau1175 : RatBall :=
  ⟨⟨41/160, 37/160⟩, 3/320⟩
def center1175 : GaussianRat :=
  ⟨182809387/1000000000, 76006029/500000000⟩
def contact1175 : RatBall := localContactBall tau1175 center1175
def work1175 : RoundedTauEval :=
  evalTau precision tau1175 contact1175 logTwoBall

theorem center_sq1175 : (center1175.re : ℝ)^2 +
    (center1175.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1175]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1175 : work1175.theta.ok = true ∧
    work1175.jac.invOK = true ∧ acceptsUnitSq work1175.out = true := by
  norm_num [work1175, contact1175, tau1175, center1175, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1175 : CellCertificate where
  tauBall := tau1175
  contactCenter := center1175
  contactBall := contact1175
  work := work1175
  center_sq := center_sq1175
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1175.1
  jac_ok := checks1175.2.1
  accepted := checks1175.2.2

def cells : List CellCertificate := [cell1168, cell1169, cell1170, cell1171, cell1172, cell1173, cell1174, cell1175]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0146
