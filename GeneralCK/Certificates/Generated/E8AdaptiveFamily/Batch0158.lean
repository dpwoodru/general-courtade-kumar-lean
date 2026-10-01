import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1264 : RatBall :=
  ⟨⟨-21/64, -71/320⟩, 3/640⟩
def center1264 : GaussianRat :=
  ⟨-45854809/200000000, -139564933/1000000000⟩
def contact1264 : RatBall := localContactBall tau1264 center1264
def work1264 : RoundedTauEval :=
  evalTau precision tau1264 contact1264 logTwoBall

theorem center_sq1264 : (center1264.re : ℝ)^2 +
    (center1264.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1264]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1264 : work1264.theta.ok = true ∧
    work1264.jac.invOK = true ∧ acceptsUnitSq work1264.out = true := by
  norm_num [work1264, contact1264, tau1264, center1264, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1264 : CellCertificate where
  tauBall := tau1264
  contactCenter := center1264
  contactBall := contact1264
  work := work1264
  center_sq := center_sq1264
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1264.1
  jac_ok := checks1264.2.1
  accepted := checks1264.2.2

def tau1265 : RatBall :=
  ⟨⟨-107/320, -69/320⟩, 3/640⟩
def center1265 : GaussianRat :=
  ⟨-58174707/250000000, -67503627/500000000⟩
def contact1265 : RatBall := localContactBall tau1265 center1265
def work1265 : RoundedTauEval :=
  evalTau precision tau1265 contact1265 logTwoBall

theorem center_sq1265 : (center1265.re : ℝ)^2 +
    (center1265.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1265]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1265 : work1265.theta.ok = true ∧
    work1265.jac.invOK = true ∧ acceptsUnitSq work1265.out = true := by
  norm_num [work1265, contact1265, tau1265, center1265, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1265 : CellCertificate where
  tauBall := tau1265
  contactCenter := center1265
  contactBall := contact1265
  work := work1265
  center_sq := center_sq1265
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1265.1
  jac_ok := checks1265.2.1
  accepted := checks1265.2.2

def tau1266 : RatBall :=
  ⟨⟨-21/64, -69/320⟩, 3/640⟩
def center1266 : GaussianRat :=
  ⟨-57177633/250000000, -13556449/100000000⟩
def contact1266 : RatBall := localContactBall tau1266 center1266
def work1266 : RoundedTauEval :=
  evalTau precision tau1266 contact1266 logTwoBall

theorem center_sq1266 : (center1266.re : ℝ)^2 +
    (center1266.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1266]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1266 : work1266.theta.ok = true ∧
    work1266.jac.invOK = true ∧ acceptsUnitSq work1266.out = true := by
  norm_num [work1266, contact1266, tau1266, center1266, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1266 : CellCertificate where
  tauBall := tau1266
  contactCenter := center1266
  contactBall := contact1266
  work := work1266
  center_sq := center_sq1266
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1266.1
  jac_ok := checks1266.2.1
  accepted := checks1266.2.2

def tau1267 : RatBall :=
  ⟨⟨-109/320, -67/320⟩, 3/640⟩
def center1267 : GaussianRat :=
  ⟨-236112247/1000000000, -65243249/500000000⟩
def contact1267 : RatBall := localContactBall tau1267 center1267
def work1267 : RoundedTauEval :=
  evalTau precision tau1267 contact1267 logTwoBall

theorem center_sq1267 : (center1267.re : ℝ)^2 +
    (center1267.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1267]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1267 : work1267.theta.ok = true ∧
    work1267.jac.invOK = true ∧ acceptsUnitSq work1267.out = true := by
  norm_num [work1267, contact1267, tau1267, center1267, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1267 : CellCertificate where
  tauBall := tau1267
  contactCenter := center1267
  contactBall := contact1267
  work := work1267
  center_sq := center_sq1267
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1267.1
  jac_ok := checks1267.2.1
  accepted := checks1267.2.2

def tau1268 : RatBall :=
  ⟨⟨-111/320, -13/64⟩, 3/640⟩
def center1268 : GaussianRat :=
  ⟨-239515009/1000000000, -31500643/250000000⟩
def contact1268 : RatBall := localContactBall tau1268 center1268
def work1268 : RoundedTauEval :=
  evalTau precision tau1268 contact1268 logTwoBall

theorem center_sq1268 : (center1268.re : ℝ)^2 +
    (center1268.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1268]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1268 : work1268.theta.ok = true ∧
    work1268.jac.invOK = true ∧ acceptsUnitSq work1268.out = true := by
  norm_num [work1268, contact1268, tau1268, center1268, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1268 : CellCertificate where
  tauBall := tau1268
  contactCenter := center1268
  contactBall := contact1268
  work := work1268
  center_sq := center_sq1268
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1268.1
  jac_ok := checks1268.2.1
  accepted := checks1268.2.2

def tau1269 : RatBall :=
  ⟨⟨-109/320, -13/64⟩, 3/640⟩
def center1269 : GaussianRat :=
  ⟨-29446781/125000000, -63266993/500000000⟩
def contact1269 : RatBall := localContactBall tau1269 center1269
def work1269 : RoundedTauEval :=
  evalTau precision tau1269 contact1269 logTwoBall

theorem center_sq1269 : (center1269.re : ℝ)^2 +
    (center1269.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1269]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1269 : work1269.theta.ok = true ∧
    work1269.jac.invOK = true ∧ acceptsUnitSq work1269.out = true := by
  norm_num [work1269, contact1269, tau1269, center1269, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1269 : CellCertificate where
  tauBall := tau1269
  contactCenter := center1269
  contactBall := contact1269
  work := work1269
  center_sq := center_sq1269
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1269.1
  jac_ok := checks1269.2.1
  accepted := checks1269.2.2

def tau1270 : RatBall :=
  ⟨⟨-89/320, -93/320⟩, 3/640⟩
def center1270 : GaussianRat :=
  ⟨-50860061/250000000, -2969643/15625000⟩
def contact1270 : RatBall := localContactBall tau1270 center1270
def work1270 : RoundedTauEval :=
  evalTau precision tau1270 contact1270 logTwoBall

theorem center_sq1270 : (center1270.re : ℝ)^2 +
    (center1270.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1270]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1270 : work1270.theta.ok = true ∧
    work1270.jac.invOK = true ∧ acceptsUnitSq work1270.out = true := by
  norm_num [work1270, contact1270, tau1270, center1270, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1270 : CellCertificate where
  tauBall := tau1270
  contactCenter := center1270
  contactBall := contact1270
  work := work1270
  center_sq := center_sq1270
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1270.1
  jac_ok := checks1270.2.1
  accepted := checks1270.2.2

def tau1271 : RatBall :=
  ⟨⟨-93/320, -89/320⟩, 3/640⟩
def center1271 : GaussianRat :=
  ⟨-84181/400000, -180208911/1000000000⟩
def contact1271 : RatBall := localContactBall tau1271 center1271
def work1271 : RoundedTauEval :=
  evalTau precision tau1271 contact1271 logTwoBall

theorem center_sq1271 : (center1271.re : ℝ)^2 +
    (center1271.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1271]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1271 : work1271.theta.ok = true ∧
    work1271.jac.invOK = true ∧ acceptsUnitSq work1271.out = true := by
  norm_num [work1271, contact1271, tau1271, center1271, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1271 : CellCertificate where
  tauBall := tau1271
  contactCenter := center1271
  contactBall := contact1271
  work := work1271
  center_sq := center_sq1271
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1271.1
  jac_ok := checks1271.2.1
  accepted := checks1271.2.2

def cells : List CellCertificate := [cell1264, cell1265, cell1266, cell1267, cell1268, cell1269, cell1270, cell1271]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158
