import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1288 : RatBall :=
  ⟨⟨-83/320, -91/320⟩, 3/640⟩
def center1288 : GaussianRat :=
  ⟨-37988073/200000000, -37573667/200000000⟩
def contact1288 : RatBall := localContactBall tau1288 center1288
def work1288 : RoundedTauEval :=
  evalTau precision tau1288 contact1288 logTwoBall

theorem center_sq1288 : (center1288.re : ℝ)^2 +
    (center1288.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1288]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1288 : work1288.theta.ok = true ∧
    work1288.jac.invOK = true ∧ acceptsUnitSq work1288.out = true := by
  norm_num [work1288, contact1288, tau1288, center1288, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1288 : CellCertificate where
  tauBall := tau1288
  contactCenter := center1288
  contactBall := contact1288
  work := work1288
  center_sq := center_sq1288
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1288.1
  jac_ok := checks1288.2.1
  accepted := checks1288.2.2

def tau1289 : RatBall :=
  ⟨⟨-81/320, -91/320⟩, 3/640⟩
def center1289 : GaussianRat :=
  ⟨-23204849/125000000, -94265223/500000000⟩
def contact1289 : RatBall := localContactBall tau1289 center1289
def work1289 : RoundedTauEval :=
  evalTau precision tau1289 contact1289 logTwoBall

theorem center_sq1289 : (center1289.re : ℝ)^2 +
    (center1289.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1289]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1289 : work1289.theta.ok = true ∧
    work1289.jac.invOK = true ∧ acceptsUnitSq work1289.out = true := by
  norm_num [work1289, contact1289, tau1289, center1289, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1289 : CellCertificate where
  tauBall := tau1289
  contactCenter := center1289
  contactBall := contact1289
  work := work1289
  center_sq := center_sq1289
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1289.1
  jac_ok := checks1289.2.1
  accepted := checks1289.2.2

def tau1290 : RatBall :=
  ⟨⟨-83/320, -89/320⟩, 3/640⟩
def center1290 : GaussianRat :=
  ⟨-189282071/1000000000, -183581561/1000000000⟩
def contact1290 : RatBall := localContactBall tau1290 center1290
def work1290 : RoundedTauEval :=
  evalTau precision tau1290 contact1290 logTwoBall

theorem center_sq1290 : (center1290.re : ℝ)^2 +
    (center1290.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1290]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1290 : work1290.theta.ok = true ∧
    work1290.jac.invOK = true ∧ acceptsUnitSq work1290.out = true := by
  norm_num [work1290, contact1290, tau1290, center1290, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1290 : CellCertificate where
  tauBall := tau1290
  contactCenter := center1290
  contactBall := contact1290
  work := work1290
  center_sq := center_sq1290
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1290.1
  jac_ok := checks1290.2.1
  accepted := checks1290.2.2

def tau1291 : RatBall :=
  ⟨⟨-81/320, -89/320⟩, 3/640⟩
def center1291 : GaussianRat :=
  ⟨-92495743/500000000, -184225151/1000000000⟩
def contact1291 : RatBall := localContactBall tau1291 center1291
def work1291 : RoundedTauEval :=
  evalTau precision tau1291 contact1291 logTwoBall

theorem center_sq1291 : (center1291.re : ℝ)^2 +
    (center1291.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1291]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1291 : work1291.theta.ok = true ∧
    work1291.jac.invOK = true ∧ acceptsUnitSq work1291.out = true := by
  norm_num [work1291, contact1291, tau1291, center1291, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1291 : CellCertificate where
  tauBall := tau1291
  contactCenter := center1291
  contactBall := contact1291
  work := work1291
  center_sq := center_sq1291
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1291.1
  jac_ok := checks1291.2.1
  accepted := checks1291.2.2

def tau1292 : RatBall :=
  ⟨⟨-19/64, -87/320⟩, 3/640⟩
def center1292 : GaussianRat :=
  ⟨-106965213/500000000, -35068781/200000000⟩
def contact1292 : RatBall := localContactBall tau1292 center1292
def work1292 : RoundedTauEval :=
  evalTau precision tau1292 contact1292 logTwoBall

theorem center_sq1292 : (center1292.re : ℝ)^2 +
    (center1292.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1292]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1292 : work1292.theta.ok = true ∧
    work1292.jac.invOK = true ∧ acceptsUnitSq work1292.out = true := by
  norm_num [work1292, contact1292, tau1292, center1292, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1292 : CellCertificate where
  tauBall := tau1292
  contactCenter := center1292
  contactBall := contact1292
  work := work1292
  center_sq := center_sq1292
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1292.1
  jac_ok := checks1292.2.1
  accepted := checks1292.2.2

def tau1293 : RatBall :=
  ⟨⟨-93/320, -87/320⟩, 3/640⟩
def center1293 : GaussianRat :=
  ⟨-1638777/7812500, -17602767/100000000⟩
def contact1293 : RatBall := localContactBall tau1293 center1293
def work1293 : RoundedTauEval :=
  evalTau precision tau1293 contact1293 logTwoBall

theorem center_sq1293 : (center1293.re : ℝ)^2 +
    (center1293.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1293]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1293 : work1293.theta.ok = true ∧
    work1293.jac.invOK = true ∧ acceptsUnitSq work1293.out = true := by
  norm_num [work1293, contact1293, tau1293, center1293, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1293 : CellCertificate where
  tauBall := tau1293
  contactCenter := center1293
  contactBall := contact1293
  work := work1293
  center_sq := center_sq1293
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1293.1
  jac_ok := checks1293.2.1
  accepted := checks1293.2.2

def tau1294 : RatBall :=
  ⟨⟨-19/64, -17/64⟩, 3/640⟩
def center1294 : GaussianRat :=
  ⟨-42650399/200000000, -171191029/1000000000⟩
def contact1294 : RatBall := localContactBall tau1294 center1294
def work1294 : RoundedTauEval :=
  evalTau precision tau1294 contact1294 logTwoBall

theorem center_sq1294 : (center1294.re : ℝ)^2 +
    (center1294.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1294]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1294 : work1294.theta.ok = true ∧
    work1294.jac.invOK = true ∧ acceptsUnitSq work1294.out = true := by
  norm_num [work1294, contact1294, tau1294, center1294, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1294 : CellCertificate where
  tauBall := tau1294
  contactCenter := center1294
  contactBall := contact1294
  work := work1294
  center_sq := center_sq1294
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1294.1
  jac_ok := checks1294.2.1
  accepted := checks1294.2.2

def tau1295 : RatBall :=
  ⟨⟨-93/320, -17/64⟩, 3/640⟩
def center1295 : GaussianRat :=
  ⟨-104546899/500000000, -171855447/1000000000⟩
def contact1295 : RatBall := localContactBall tau1295 center1295
def work1295 : RoundedTauEval :=
  evalTau precision tau1295 contact1295 logTwoBall

theorem center_sq1295 : (center1295.re : ℝ)^2 +
    (center1295.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1295]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1295 : work1295.theta.ok = true ∧
    work1295.jac.invOK = true ∧ acceptsUnitSq work1295.out = true := by
  norm_num [work1295, contact1295, tau1295, center1295, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1295 : CellCertificate where
  tauBall := tau1295
  contactCenter := center1295
  contactBall := contact1295
  work := work1295
  center_sq := center_sq1295
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1295.1
  jac_ok := checks1295.2.1
  accepted := checks1295.2.2

def cells : List CellCertificate := [cell1288, cell1289, cell1290, cell1291, cell1292, cell1293, cell1294, cell1295]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161
