import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1144 : RatBall :=
  ⟨⟨19/160, 51/160⟩, 3/320⟩
def center1144 : GaussianRat :=
  ⟨18258621/200000000, 56322187/250000000⟩
def contact1144 : RatBall := localContactBall tau1144 center1144
def work1144 : RoundedTauEval :=
  evalTau precision tau1144 contact1144 logTwoBall

theorem center_sq1144 : (center1144.re : ℝ)^2 +
    (center1144.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1144]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1144 : work1144.theta.ok = true ∧
    work1144.jac.invOK = true ∧ acceptsUnitSq work1144.out = true := by
  norm_num [work1144, contact1144, tau1144, center1144, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1144 : CellCertificate where
  tauBall := tau1144
  contactCenter := center1144
  contactBall := contact1144
  work := work1144
  center_sq := center_sq1144
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1144.1
  jac_ok := checks1144.2.1
  accepted := checks1144.2.2

def tau1145 : RatBall :=
  ⟨⟨21/160, 49/160⟩, 3/320⟩
def center1145 : GaussianRat :=
  ⟨9985979/100000000, 43011679/200000000⟩
def contact1145 : RatBall := localContactBall tau1145 center1145
def work1145 : RoundedTauEval :=
  evalTau precision tau1145 contact1145 logTwoBall

theorem center_sq1145 : (center1145.re : ℝ)^2 +
    (center1145.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1145]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1145 : work1145.theta.ok = true ∧
    work1145.jac.invOK = true ∧ acceptsUnitSq work1145.out = true := by
  norm_num [work1145, contact1145, tau1145, center1145, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1145 : CellCertificate where
  tauBall := tau1145
  contactCenter := center1145
  contactBall := contact1145
  work := work1145
  center_sq := center_sq1145
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1145.1
  jac_ok := checks1145.2.1
  accepted := checks1145.2.2

def tau1146 : RatBall :=
  ⟨⟨23/160, 49/160⟩, 3/320⟩
def center1146 : GaussianRat :=
  ⟨109172181/1000000000, 42835301/200000000⟩
def contact1146 : RatBall := localContactBall tau1146 center1146
def work1146 : RoundedTauEval :=
  evalTau precision tau1146 contact1146 logTwoBall

theorem center_sq1146 : (center1146.re : ℝ)^2 +
    (center1146.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1146]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1146 : work1146.theta.ok = true ∧
    work1146.jac.invOK = true ∧ acceptsUnitSq work1146.out = true := by
  norm_num [work1146, contact1146, tau1146, center1146, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1146 : CellCertificate where
  tauBall := tau1146
  contactCenter := center1146
  contactBall := contact1146
  work := work1146
  center_sq := center_sq1146
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1146.1
  jac_ok := checks1146.2.1
  accepted := checks1146.2.2

def tau1147 : RatBall :=
  ⟨⟨21/160, 51/160⟩, 3/320⟩
def center1147 : GaussianRat :=
  ⟨100729897/1000000000, 44886561/200000000⟩
def contact1147 : RatBall := localContactBall tau1147 center1147
def work1147 : RoundedTauEval :=
  evalTau precision tau1147 contact1147 logTwoBall

theorem center_sq1147 : (center1147.re : ℝ)^2 +
    (center1147.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1147]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1147 : work1147.theta.ok = true ∧
    work1147.jac.invOK = true ∧ acceptsUnitSq work1147.out = true := by
  norm_num [work1147, contact1147, tau1147, center1147, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1147 : CellCertificate where
  tauBall := tau1147
  contactCenter := center1147
  contactBall := contact1147
  work := work1147
  center_sq := center_sq1147
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1147.1
  jac_ok := checks1147.2.1
  accepted := checks1147.2.2

def tau1148 : RatBall :=
  ⟨⟨17/160, 53/160⟩, 3/320⟩
def center1148 : GaussianRat :=
  ⟨82567747/1000000000, 117805603/500000000⟩
def contact1148 : RatBall := localContactBall tau1148 center1148
def work1148 : RoundedTauEval :=
  evalTau precision tau1148 contact1148 logTwoBall

theorem center_sq1148 : (center1148.re : ℝ)^2 +
    (center1148.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1148]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1148 : work1148.theta.ok = true ∧
    work1148.jac.invOK = true ∧ acceptsUnitSq work1148.out = true := by
  norm_num [work1148, contact1148, tau1148, center1148, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1148 : CellCertificate where
  tauBall := tau1148
  contactCenter := center1148
  contactBall := contact1148
  work := work1148
  center_sq := center_sq1148
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1148.1
  jac_ok := checks1148.2.1
  accepted := checks1148.2.2

def tau1149 : RatBall :=
  ⟨⟨5/32, 49/160⟩, 3/320⟩
def center1149 : GaussianRat :=
  ⟨23686489/200000000, 53305887/250000000⟩
def contact1149 : RatBall := localContactBall tau1149 center1149
def work1149 : RoundedTauEval :=
  evalTau precision tau1149 contact1149 logTwoBall

theorem center_sq1149 : (center1149.re : ℝ)^2 +
    (center1149.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1149]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1149 : work1149.theta.ok = true ∧
    work1149.jac.invOK = true ∧ acceptsUnitSq work1149.out = true := by
  norm_num [work1149, contact1149, tau1149, center1149, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1149 : CellCertificate where
  tauBall := tau1149
  contactCenter := center1149
  contactBall := contact1149
  work := work1149
  center_sq := center_sq1149
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1149.1
  jac_ok := checks1149.2.1
  accepted := checks1149.2.2

def tau1150 : RatBall :=
  ⟨⟨27/160, 49/160⟩, 3/320⟩
def center1150 : GaussianRat :=
  ⟨3988651/31250000, 53050431/250000000⟩
def contact1150 : RatBall := localContactBall tau1150 center1150
def work1150 : RoundedTauEval :=
  evalTau precision tau1150 contact1150 logTwoBall

theorem center_sq1150 : (center1150.re : ℝ)^2 +
    (center1150.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1150]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1150 : work1150.theta.ok = true ∧
    work1150.jac.invOK = true ∧ acceptsUnitSq work1150.out = true := by
  norm_num [work1150, contact1150, tau1150, center1150, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1150 : CellCertificate where
  tauBall := tau1150
  contactCenter := center1150
  contactBall := contact1150
  work := work1150
  center_sq := center_sq1150
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1150.1
  jac_ok := checks1150.2.1
  accepted := checks1150.2.2

def tau1151 : RatBall :=
  ⟨⟨33/160, 33/160⟩, 3/320⟩
def center1151 : GaussianRat :=
  ⟨73472183/500000000, 69270487/500000000⟩
def contact1151 : RatBall := localContactBall tau1151 center1151
def work1151 : RoundedTauEval :=
  evalTau precision tau1151 contact1151 logTwoBall

theorem center_sq1151 : (center1151.re : ℝ)^2 +
    (center1151.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1151]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1151 : work1151.theta.ok = true ∧
    work1151.jac.invOK = true ∧ acceptsUnitSq work1151.out = true := by
  norm_num [work1151, contact1151, tau1151, center1151, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1151 : CellCertificate where
  tauBall := tau1151
  contactCenter := center1151
  contactBall := contact1151
  work := work1151
  center_sq := center_sq1151
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1151.1
  jac_ok := checks1151.2.1
  accepted := checks1151.2.2

def cells : List CellCertificate := [cell1144, cell1145, cell1146, cell1147, cell1148, cell1149, cell1150, cell1151]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143
