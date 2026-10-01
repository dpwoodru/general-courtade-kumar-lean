import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1080 : RatBall :=
  ⟨⟨19/160, 41/160⟩, 3/320⟩
def center1080 : GaussianRat :=
  ⟨43873979/500000000, 35778323/200000000⟩
def contact1080 : RatBall := localContactBall tau1080 center1080
def work1080 : RoundedTauEval :=
  evalTau precision tau1080 contact1080 logTwoBall

theorem center_sq1080 : (center1080.re : ℝ)^2 +
    (center1080.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1080]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1080 : work1080.theta.ok = true ∧
    work1080.jac.invOK = true ∧ acceptsUnitSq work1080.out = true := by
  norm_num [work1080, contact1080, tau1080, center1080, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1080 : CellCertificate where
  tauBall := tau1080
  contactCenter := center1080
  contactBall := contact1080
  work := work1080
  center_sq := center_sq1080
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1080.1
  jac_ok := checks1080.2.1
  accepted := checks1080.2.2

def tau1081 : RatBall :=
  ⟨⟨17/160, 43/160⟩, 3/320⟩
def center1081 : GaussianRat :=
  ⟨39590143/500000000, 47162917/250000000⟩
def contact1081 : RatBall := localContactBall tau1081 center1081
def work1081 : RoundedTauEval :=
  evalTau precision tau1081 contact1081 logTwoBall

theorem center_sq1081 : (center1081.re : ℝ)^2 +
    (center1081.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1081]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1081 : work1081.theta.ok = true ∧
    work1081.jac.invOK = true ∧ acceptsUnitSq work1081.out = true := by
  norm_num [work1081, contact1081, tau1081, center1081, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1081 : CellCertificate where
  tauBall := tau1081
  contactCenter := center1081
  contactBall := contact1081
  work := work1081
  center_sq := center_sq1081
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1081.1
  jac_ok := checks1081.2.1
  accepted := checks1081.2.2

def tau1082 : RatBall :=
  ⟨⟨19/160, 43/160⟩, 3/320⟩
def center1082 : GaussianRat :=
  ⟨88375401/1000000000, 188036739/1000000000⟩
def contact1082 : RatBall := localContactBall tau1082 center1082
def work1082 : RoundedTauEval :=
  evalTau precision tau1082 contact1082 logTwoBall

theorem center_sq1082 : (center1082.re : ℝ)^2 +
    (center1082.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1082]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1082 : work1082.theta.ok = true ∧
    work1082.jac.invOK = true ∧ acceptsUnitSq work1082.out = true := by
  norm_num [work1082, contact1082, tau1082, center1082, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1082 : CellCertificate where
  tauBall := tau1082
  contactCenter := center1082
  contactBall := contact1082
  work := work1082
  center_sq := center_sq1082
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1082.1
  jac_ok := checks1082.2.1
  accepted := checks1082.2.2

def tau1083 : RatBall :=
  ⟨⟨21/160, 41/160⟩, 3/320⟩
def center1083 : GaussianRat :=
  ⟨96843181/1000000000, 5570429/31250000⟩
def contact1083 : RatBall := localContactBall tau1083 center1083
def work1083 : RoundedTauEval :=
  evalTau precision tau1083 contact1083 logTwoBall

theorem center_sq1083 : (center1083.re : ℝ)^2 +
    (center1083.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1083]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1083 : work1083.theta.ok = true ∧
    work1083.jac.invOK = true ∧ acceptsUnitSq work1083.out = true := by
  norm_num [work1083, contact1083, tau1083, center1083, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1083 : CellCertificate where
  tauBall := tau1083
  contactCenter := center1083
  contactBall := contact1083
  work := work1083
  center_sq := center_sq1083
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1083.1
  jac_ok := checks1083.2.1
  accepted := checks1083.2.2

def tau1084 : RatBall :=
  ⟨⟨23/160, 41/160⟩, 3/320⟩
def center1084 : GaussianRat :=
  ⟨105897059/1000000000, 22194707/125000000⟩
def contact1084 : RatBall := localContactBall tau1084 center1084
def work1084 : RoundedTauEval :=
  evalTau precision tau1084 contact1084 logTwoBall

theorem center_sq1084 : (center1084.re : ℝ)^2 +
    (center1084.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1084]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1084 : work1084.theta.ok = true ∧
    work1084.jac.invOK = true ∧ acceptsUnitSq work1084.out = true := by
  norm_num [work1084, contact1084, tau1084, center1084, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1084 : CellCertificate where
  tauBall := tau1084
  contactCenter := center1084
  contactBall := contact1084
  work := work1084
  center_sq := center_sq1084
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1084.1
  jac_ok := checks1084.2.1
  accepted := checks1084.2.2

def tau1085 : RatBall :=
  ⟨⟨21/160, 43/160⟩, 3/320⟩
def center1085 : GaussianRat :=
  ⟨1523927/15625000, 46839637/250000000⟩
def contact1085 : RatBall := localContactBall tau1085 center1085
def work1085 : RoundedTauEval :=
  evalTau precision tau1085 contact1085 logTwoBall

theorem center_sq1085 : (center1085.re : ℝ)^2 +
    (center1085.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1085]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1085 : work1085.theta.ok = true ∧
    work1085.jac.invOK = true ∧ acceptsUnitSq work1085.out = true := by
  norm_num [work1085, contact1085, tau1085, center1085, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1085 : CellCertificate where
  tauBall := tau1085
  contactCenter := center1085
  contactBall := contact1085
  work := work1085
  center_sq := center_sq1085
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1085.1
  jac_ok := checks1085.2.1
  accepted := checks1085.2.2

def tau1086 : RatBall :=
  ⟨⟨23/160, 43/160⟩, 3/320⟩
def center1086 : GaussianRat :=
  ⟨106644393/1000000000, 93309307/500000000⟩
def contact1086 : RatBall := localContactBall tau1086 center1086
def work1086 : RoundedTauEval :=
  evalTau precision tau1086 contact1086 logTwoBall

theorem center_sq1086 : (center1086.re : ℝ)^2 +
    (center1086.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1086]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1086 : work1086.theta.ok = true ∧
    work1086.jac.invOK = true ∧ acceptsUnitSq work1086.out = true := by
  norm_num [work1086, contact1086, tau1086, center1086, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1086 : CellCertificate where
  tauBall := tau1086
  contactCenter := center1086
  contactBall := contact1086
  work := work1086
  center_sq := center_sq1086
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1086.1
  jac_ok := checks1086.2.1
  accepted := checks1086.2.2

def tau1087 : RatBall :=
  ⟨⟨17/160, 9/32⟩, 3/320⟩
def center1087 : GaussianRat :=
  ⟨19945259/250000000, 39579621/200000000⟩
def contact1087 : RatBall := localContactBall tau1087 center1087
def work1087 : RoundedTauEval :=
  evalTau precision tau1087 contact1087 logTwoBall

theorem center_sq1087 : (center1087.re : ℝ)^2 +
    (center1087.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1087]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1087 : work1087.theta.ok = true ∧
    work1087.jac.invOK = true ∧ acceptsUnitSq work1087.out = true := by
  norm_num [work1087, contact1087, tau1087, center1087, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1087 : CellCertificate where
  tauBall := tau1087
  contactCenter := center1087
  contactBall := contact1087
  work := work1087
  center_sq := center_sq1087
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1087.1
  jac_ok := checks1087.2.1
  accepted := checks1087.2.2

def cells : List CellCertificate := [cell1080, cell1081, cell1082, cell1083, cell1084, cell1085, cell1086, cell1087]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135
