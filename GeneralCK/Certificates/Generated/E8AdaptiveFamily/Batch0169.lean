import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1352 : RatBall :=
  ⟨⟨-43/320, -113/320⟩, 3/640⟩
def center1352 : GaussianRat :=
  ⟨-105797499/1000000000, -62590039/250000000⟩
def contact1352 : RatBall := localContactBall tau1352 center1352
def work1352 : RoundedTauEval :=
  evalTau precision tau1352 contact1352 logTwoBall

theorem center_sq1352 : (center1352.re : ℝ)^2 +
    (center1352.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1352]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1352 : work1352.theta.ok = true ∧
    work1352.jac.invOK = true ∧ acceptsUnitSq work1352.out = true := by
  norm_num [work1352, contact1352, tau1352, center1352, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1352 : CellCertificate where
  tauBall := tau1352
  contactCenter := center1352
  contactBall := contact1352
  work := work1352
  center_sq := center_sq1352
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1352.1
  jac_ok := checks1352.2.1
  accepted := checks1352.2.2

def tau1353 : RatBall :=
  ⟨⟨-41/320, -113/320⟩, 3/640⟩
def center1353 : GaussianRat :=
  ⟨-100977067/1000000000, -250881183/1000000000⟩
def contact1353 : RatBall := localContactBall tau1353 center1353
def work1353 : RoundedTauEval :=
  evalTau precision tau1353 contact1353 logTwoBall

theorem center_sq1353 : (center1353.re : ℝ)^2 +
    (center1353.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1353]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1353 : work1353.theta.ok = true ∧
    work1353.jac.invOK = true ∧ acceptsUnitSq work1353.out = true := by
  norm_num [work1353, contact1353, tau1353, center1353, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1353 : CellCertificate where
  tauBall := tau1353
  contactCenter := center1353
  contactBall := contact1353
  work := work1353
  center_sq := center_sq1353
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1353.1
  jac_ok := checks1353.2.1
  accepted := checks1353.2.2

def tau1354 : RatBall :=
  ⟨⟨-39/320, -117/320⟩, 3/640⟩
def center1354 : GaussianRat :=
  ⟨-97144261/1000000000, -261108469/1000000000⟩
def contact1354 : RatBall := localContactBall tau1354 center1354
def work1354 : RoundedTauEval :=
  evalTau precision tau1354 contact1354 logTwoBall

theorem center_sq1354 : (center1354.re : ℝ)^2 +
    (center1354.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1354]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1354 : work1354.theta.ok = true ∧
    work1354.jac.invOK = true ∧ acceptsUnitSq work1354.out = true := by
  norm_num [work1354, contact1354, tau1354, center1354, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1354 : CellCertificate where
  tauBall := tau1354
  contactCenter := center1354
  contactBall := contact1354
  work := work1354
  center_sq := center_sq1354
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1354.1
  jac_ok := checks1354.2.1
  accepted := checks1354.2.2

def tau1355 : RatBall :=
  ⟨⟨-37/320, -117/320⟩, 3/640⟩
def center1355 : GaussianRat :=
  ⟨-46124689/500000000, -261610997/1000000000⟩
def contact1355 : RatBall := localContactBall tau1355 center1355
def work1355 : RoundedTauEval :=
  evalTau precision tau1355 contact1355 logTwoBall

theorem center_sq1355 : (center1355.re : ℝ)^2 +
    (center1355.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1355]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1355 : work1355.theta.ok = true ∧
    work1355.jac.invOK = true ∧ acceptsUnitSq work1355.out = true := by
  norm_num [work1355, contact1355, tau1355, center1355, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1355 : CellCertificate where
  tauBall := tau1355
  contactCenter := center1355
  contactBall := contact1355
  work := work1355
  center_sq := center_sq1355
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1355.1
  jac_ok := checks1355.2.1
  accepted := checks1355.2.2

def tau1356 : RatBall :=
  ⟨⟨-7/64, -117/320⟩, 3/640⟩
def center1356 : GaussianRat :=
  ⟨-43670547/500000000, -65522293/250000000⟩
def contact1356 : RatBall := localContactBall tau1356 center1356
def work1356 : RoundedTauEval :=
  evalTau precision tau1356 contact1356 logTwoBall

theorem center_sq1356 : (center1356.re : ℝ)^2 +
    (center1356.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1356]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1356 : work1356.theta.ok = true ∧
    work1356.jac.invOK = true ∧ acceptsUnitSq work1356.out = true := by
  norm_num [work1356, contact1356, tau1356, center1356, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1356 : CellCertificate where
  tauBall := tau1356
  contactCenter := center1356
  contactBall := contact1356
  work := work1356
  center_sq := center_sq1356
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1356.1
  jac_ok := checks1356.2.1
  accepted := checks1356.2.2

def tau1357 : RatBall :=
  ⟨⟨-33/320, -117/320⟩, 3/640⟩
def center1357 : GaussianRat :=
  ⟨-1648401/20000000, -65635667/250000000⟩
def contact1357 : RatBall := localContactBall tau1357 center1357
def work1357 : RoundedTauEval :=
  evalTau precision tau1357 contact1357 logTwoBall

theorem center_sq1357 : (center1357.re : ℝ)^2 +
    (center1357.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1357]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1357 : work1357.theta.ok = true ∧
    work1357.jac.invOK = true ∧ acceptsUnitSq work1357.out = true := by
  norm_num [work1357, contact1357, tau1357, center1357, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1357 : CellCertificate where
  tauBall := tau1357
  contactCenter := center1357
  contactBall := contact1357
  work := work1357
  center_sq := center_sq1357
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1357.1
  jac_ok := checks1357.2.1
  accepted := checks1357.2.2

def tau1358 : RatBall :=
  ⟨⟨-39/320, -23/64⟩, 3/640⟩
def center1358 : GaussianRat :=
  ⟨-773093/8000000, -128116201/500000000⟩
def contact1358 : RatBall := localContactBall tau1358 center1358
def work1358 : RoundedTauEval :=
  evalTau precision tau1358 contact1358 logTwoBall

theorem center_sq1358 : (center1358.re : ℝ)^2 +
    (center1358.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1358]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1358 : work1358.theta.ok = true ∧
    work1358.jac.invOK = true ∧ acceptsUnitSq work1358.out = true := by
  norm_num [work1358, contact1358, tau1358, center1358, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1358 : CellCertificate where
  tauBall := tau1358
  contactCenter := center1358
  contactBall := contact1358
  work := work1358
  center_sq := center_sq1358
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1358.1
  jac_ok := checks1358.2.1
  accepted := checks1358.2.2

def tau1359 : RatBall :=
  ⟨⟨-37/320, -23/64⟩, 3/640⟩
def center1359 : GaussianRat :=
  ⟨-91765617/1000000000, -12836069/50000000⟩
def contact1359 : RatBall := localContactBall tau1359 center1359
def work1359 : RoundedTauEval :=
  evalTau precision tau1359 contact1359 logTwoBall

theorem center_sq1359 : (center1359.re : ℝ)^2 +
    (center1359.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1359]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1359 : work1359.theta.ok = true ∧
    work1359.jac.invOK = true ∧ acceptsUnitSq work1359.out = true := by
  norm_num [work1359, contact1359, tau1359, center1359, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1359 : CellCertificate where
  tauBall := tau1359
  contactCenter := center1359
  contactBall := contact1359
  work := work1359
  center_sq := center_sq1359
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1359.1
  jac_ok := checks1359.2.1
  accepted := checks1359.2.2

def cells : List CellCertificate := [cell1352, cell1353, cell1354, cell1355, cell1356, cell1357, cell1358, cell1359]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169
