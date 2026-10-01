import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1312 : RatBall :=
  ⟨⟨-83/320, -87/320⟩, 3/640⟩
def center1312 : GaussianRat :=
  ⟨-188642281/1000000000, -22413187/125000000⟩
def contact1312 : RatBall := localContactBall tau1312 center1312
def work1312 : RoundedTauEval :=
  evalTau precision tau1312 contact1312 logTwoBall

theorem center_sq1312 : (center1312.re : ℝ)^2 +
    (center1312.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1312]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1312 : work1312.theta.ok = true ∧
    work1312.jac.invOK = true ∧ acceptsUnitSq work1312.out = true := by
  norm_num [work1312, contact1312, tau1312, center1312, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1312 : CellCertificate where
  tauBall := tau1312
  contactCenter := center1312
  contactBall := contact1312
  work := work1312
  center_sq := center_sq1312
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1312.1
  jac_ok := checks1312.2.1
  accepted := checks1312.2.2

def tau1313 : RatBall :=
  ⟨⟨-81/320, -87/320⟩, 3/640⟩
def center1313 : GaussianRat :=
  ⟨-9218121/50000000, -179930859/1000000000⟩
def contact1313 : RatBall := localContactBall tau1313 center1313
def work1313 : RoundedTauEval :=
  evalTau precision tau1313 contact1313 logTwoBall

theorem center_sq1313 : (center1313.re : ℝ)^2 +
    (center1313.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1313]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1313 : work1313.theta.ok = true ∧
    work1313.jac.invOK = true ∧ acceptsUnitSq work1313.out = true := by
  norm_num [work1313, contact1313, tau1313, center1313, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1313 : CellCertificate where
  tauBall := tau1313
  contactCenter := center1313
  contactBall := contact1313
  work := work1313
  center_sq := center_sq1313
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1313.1
  jac_ok := checks1313.2.1
  accepted := checks1313.2.2

def tau1314 : RatBall :=
  ⟨⟨-83/320, -17/64⟩, 3/640⟩
def center1314 : GaussianRat :=
  ⟨-188020707/1000000000, -4375997/25000000⟩
def contact1314 : RatBall := localContactBall tau1314 center1314
def work1314 : RoundedTauEval :=
  evalTau precision tau1314 contact1314 logTwoBall

theorem center_sq1314 : (center1314.re : ℝ)^2 +
    (center1314.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1314]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1314 : work1314.theta.ok = true ∧
    work1314.jac.invOK = true ∧ acceptsUnitSq work1314.out = true := by
  norm_num [work1314, contact1314, tau1314, center1314, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1314 : CellCertificate where
  tauBall := tau1314
  contactCenter := center1314
  contactBall := contact1314
  work := work1314
  center_sq := center_sq1314
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1314.1
  jac_ok := checks1314.2.1
  accepted := checks1314.2.2

def tau1315 : RatBall :=
  ⟨⟨-81/320, -17/64⟩, 3/640⟩
def center1315 : GaussianRat :=
  ⟨-36750261/200000000, -1756473/10000000⟩
def contact1315 : RatBall := localContactBall tau1315 center1315
def work1315 : RoundedTauEval :=
  evalTau precision tau1315 contact1315 logTwoBall

theorem center_sq1315 : (center1315.re : ℝ)^2 +
    (center1315.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1315]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1315 : work1315.theta.ok = true ∧
    work1315.jac.invOK = true ∧ acceptsUnitSq work1315.out = true := by
  norm_num [work1315, contact1315, tau1315, center1315, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1315 : CellCertificate where
  tauBall := tau1315
  contactCenter := center1315
  contactBall := contact1315
  work := work1315
  center_sq := center_sq1315
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1315.1
  jac_ok := checks1315.2.1
  accepted := checks1315.2.2

def tau1316 : RatBall :=
  ⟨⟨-79/320, -19/64⟩, 3/640⟩
def center1316 : GaussianRat :=
  ⟨-91322907/500000000, -98931697/500000000⟩
def contact1316 : RatBall := localContactBall tau1316 center1316
def work1316 : RoundedTauEval :=
  evalTau precision tau1316 contact1316 logTwoBall

theorem center_sq1316 : (center1316.re : ℝ)^2 +
    (center1316.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1316]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1316 : work1316.theta.ok = true ∧
    work1316.jac.invOK = true ∧ acceptsUnitSq work1316.out = true := by
  norm_num [work1316, contact1316, tau1316, center1316, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1316 : CellCertificate where
  tauBall := tau1316
  contactCenter := center1316
  contactBall := contact1316
  work := work1316
  center_sq := center_sq1316
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1316.1
  jac_ok := checks1316.2.1
  accepted := checks1316.2.2

def tau1317 : RatBall :=
  ⟨⟨-77/320, -19/64⟩, 3/640⟩
def center1317 : GaussianRat :=
  ⟨-35656681/200000000, -198539511/1000000000⟩
def contact1317 : RatBall := localContactBall tau1317 center1317
def work1317 : RoundedTauEval :=
  evalTau precision tau1317 contact1317 logTwoBall

theorem center_sq1317 : (center1317.re : ℝ)^2 +
    (center1317.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1317]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1317 : work1317.theta.ok = true ∧
    work1317.jac.invOK = true ∧ acceptsUnitSq work1317.out = true := by
  norm_num [work1317, contact1317, tau1317, center1317, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1317 : CellCertificate where
  tauBall := tau1317
  contactCenter := center1317
  contactBall := contact1317
  work := work1317
  center_sq := center_sq1317
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1317.1
  jac_ok := checks1317.2.1
  accepted := checks1317.2.2

def tau1318 : RatBall :=
  ⟨⟨-79/320, -93/320⟩, 3/640⟩
def center1318 : GaussianRat :=
  ⟨-90986481/500000000, -24189551/125000000⟩
def contact1318 : RatBall := localContactBall tau1318 center1318
def work1318 : RoundedTauEval :=
  evalTau precision tau1318 contact1318 logTwoBall

theorem center_sq1318 : (center1318.re : ℝ)^2 +
    (center1318.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1318]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1318 : work1318.theta.ok = true ∧
    work1318.jac.invOK = true ∧ acceptsUnitSq work1318.out = true := by
  norm_num [work1318, contact1318, tau1318, center1318, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1318 : CellCertificate where
  tauBall := tau1318
  contactCenter := center1318
  contactBall := contact1318
  work := work1318
  center_sq := center_sq1318
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1318.1
  jac_ok := checks1318.2.1
  accepted := checks1318.2.2

def tau1319 : RatBall :=
  ⟨⟨-77/320, -93/320⟩, 3/640⟩
def center1319 : GaussianRat :=
  ⟨-44405679/250000000, -194173939/1000000000⟩
def contact1319 : RatBall := localContactBall tau1319 center1319
def work1319 : RoundedTauEval :=
  evalTau precision tau1319 contact1319 logTwoBall

theorem center_sq1319 : (center1319.re : ℝ)^2 +
    (center1319.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1319]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1319 : work1319.theta.ok = true ∧
    work1319.jac.invOK = true ∧ acceptsUnitSq work1319.out = true := by
  norm_num [work1319, contact1319, tau1319, center1319, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1319 : CellCertificate where
  tauBall := tau1319
  contactCenter := center1319
  contactBall := contact1319
  work := work1319
  center_sq := center_sq1319
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1319.1
  jac_ok := checks1319.2.1
  accepted := checks1319.2.2

def cells : List CellCertificate := [cell1312, cell1313, cell1314, cell1315, cell1316, cell1317, cell1318, cell1319]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164
