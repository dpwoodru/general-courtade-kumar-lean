import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1280 : RatBall :=
  ⟨⟨-83/320, -19/64⟩, 3/640⟩
def center1280 : GaussianRat :=
  ⟨-191313683/1000000000, -3929501/20000000⟩
def contact1280 : RatBall := localContactBall tau1280 center1280
def work1280 : RoundedTauEval :=
  evalTau precision tau1280 contact1280 logTwoBall

theorem center_sq1280 : (center1280.re : ℝ)^2 +
    (center1280.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1280]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1280 : work1280.theta.ok = true ∧
    work1280.jac.invOK = true ∧ acceptsUnitSq work1280.out = true := by
  norm_num [work1280, contact1280, tau1280, center1280, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1280 : CellCertificate where
  tauBall := tau1280
  contactCenter := center1280
  contactBall := contact1280
  work := work1280
  center_sq := center_sq1280
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1280.1
  jac_ok := checks1280.2.1
  accepted := checks1280.2.2

def tau1281 : RatBall :=
  ⟨⟨-81/320, -19/64⟩, 3/640⟩
def center1281 : GaussianRat :=
  ⟨-186989333/1000000000, -49293783/250000000⟩
def contact1281 : RatBall := localContactBall tau1281 center1281
def work1281 : RoundedTauEval :=
  evalTau precision tau1281 contact1281 logTwoBall

theorem center_sq1281 : (center1281.re : ℝ)^2 +
    (center1281.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1281]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1281 : work1281.theta.ok = true ∧
    work1281.jac.invOK = true ∧ acceptsUnitSq work1281.out = true := by
  norm_num [work1281, contact1281, tau1281, center1281, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1281 : CellCertificate where
  tauBall := tau1281
  contactCenter := center1281
  contactBall := contact1281
  work := work1281
  center_sq := center_sq1281
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1281.1
  jac_ok := checks1281.2.1
  accepted := checks1281.2.2

def tau1282 : RatBall :=
  ⟨⟨-83/320, -93/320⟩, 3/640⟩
def center1282 : GaussianRat :=
  ⟨-95308733/500000000, -192166077/1000000000⟩
def contact1282 : RatBall := localContactBall tau1282 center1282
def work1282 : RoundedTauEval :=
  evalTau precision tau1282 contact1282 logTwoBall

theorem center_sq1282 : (center1282.re : ℝ)^2 +
    (center1282.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1282]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1282 : work1282.theta.ok = true ∧
    work1282.jac.invOK = true ∧ acceptsUnitSq work1282.out = true := by
  norm_num [work1282, contact1282, tau1282, center1282, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1282 : CellCertificate where
  tauBall := tau1282
  contactCenter := center1282
  contactBall := contact1282
  work := work1282
  center_sq := center_sq1282
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1282.1
  jac_ok := checks1282.2.1
  accepted := checks1282.2.2

def tau1283 : RatBall :=
  ⟨⟨-81/320, -93/320⟩, 3/640⟩
def center1283 : GaussianRat :=
  ⟨-93152319/500000000, -24105877/125000000⟩
def contact1283 : RatBall := localContactBall tau1283 center1283
def work1283 : RoundedTauEval :=
  evalTau precision tau1283 contact1283 logTwoBall

theorem center_sq1283 : (center1283.re : ℝ)^2 +
    (center1283.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1283]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1283 : work1283.theta.ok = true ∧
    work1283.jac.invOK = true ∧ acceptsUnitSq work1283.out = true := by
  norm_num [work1283, contact1283, tau1283, center1283, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1283 : CellCertificate where
  tauBall := tau1283
  contactCenter := center1283
  contactBall := contact1283
  work := work1283
  center_sq := center_sq1283
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1283.1
  jac_ok := checks1283.2.1
  accepted := checks1283.2.2

def tau1284 : RatBall :=
  ⟨⟨-87/320, -91/320⟩, 3/640⟩
def center1284 : GaussianRat :=
  ⟨-49621711/250000000, -186511513/1000000000⟩
def contact1284 : RatBall := localContactBall tau1284 center1284
def work1284 : RoundedTauEval :=
  evalTau precision tau1284 contact1284 logTwoBall

theorem center_sq1284 : (center1284.re : ℝ)^2 +
    (center1284.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1284]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1284 : work1284.theta.ok = true ∧
    work1284.jac.invOK = true ∧ acceptsUnitSq work1284.out = true := by
  norm_num [work1284, contact1284, tau1284, center1284, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1284 : CellCertificate where
  tauBall := tau1284
  contactCenter := center1284
  contactBall := contact1284
  work := work1284
  center_sq := center_sq1284
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1284.1
  jac_ok := checks1284.2.1
  accepted := checks1284.2.2

def tau1285 : RatBall :=
  ⟨⟨-17/64, -91/320⟩, 3/640⟩
def center1285 : GaussianRat :=
  ⟨-97111567/500000000, -37439051/200000000⟩
def contact1285 : RatBall := localContactBall tau1285 center1285
def work1285 : RoundedTauEval :=
  evalTau precision tau1285 contact1285 logTwoBall

theorem center_sq1285 : (center1285.re : ℝ)^2 +
    (center1285.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1285]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1285 : work1285.theta.ok = true ∧
    work1285.jac.invOK = true ∧ acceptsUnitSq work1285.out = true := by
  norm_num [work1285, contact1285, tau1285, center1285, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1285 : CellCertificate where
  tauBall := tau1285
  contactCenter := center1285
  contactBall := contact1285
  work := work1285
  center_sq := center_sq1285
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1285.1
  jac_ok := checks1285.2.1
  accepted := checks1285.2.2

def tau1286 : RatBall :=
  ⟨⟨-87/320, -89/320⟩, 3/640⟩
def center1286 : GaussianRat :=
  ⟨-7912299/40000000, -91131277/500000000⟩
def contact1286 : RatBall := localContactBall tau1286 center1286
def work1286 : RoundedTauEval :=
  evalTau precision tau1286 contact1286 logTwoBall

theorem center_sq1286 : (center1286.re : ℝ)^2 +
    (center1286.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1286]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1286 : work1286.theta.ok = true ∧
    work1286.jac.invOK = true ∧ acceptsUnitSq work1286.out = true := by
  norm_num [work1286, contact1286, tau1286, center1286, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1286 : CellCertificate where
  tauBall := tau1286
  contactCenter := center1286
  contactBall := contact1286
  work := work1286
  center_sq := center_sq1286
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1286.1
  jac_ok := checks1286.2.1
  accepted := checks1286.2.2

def tau1287 : RatBall :=
  ⟨⟨-17/64, -89/320⟩, 3/640⟩
def center1287 : GaussianRat :=
  ⟨-24194269/125000000, -5716477/31250000⟩
def contact1287 : RatBall := localContactBall tau1287 center1287
def work1287 : RoundedTauEval :=
  evalTau precision tau1287 contact1287 logTwoBall

theorem center_sq1287 : (center1287.re : ℝ)^2 +
    (center1287.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1287]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1287 : work1287.theta.ok = true ∧
    work1287.jac.invOK = true ∧ acceptsUnitSq work1287.out = true := by
  norm_num [work1287, contact1287, tau1287, center1287, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1287 : CellCertificate where
  tauBall := tau1287
  contactCenter := center1287
  contactBall := contact1287
  work := work1287
  center_sq := center_sq1287
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1287.1
  jac_ok := checks1287.2.1
  accepted := checks1287.2.2

def cells : List CellCertificate := [cell1280, cell1281, cell1282, cell1283, cell1284, cell1285, cell1286, cell1287]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160
