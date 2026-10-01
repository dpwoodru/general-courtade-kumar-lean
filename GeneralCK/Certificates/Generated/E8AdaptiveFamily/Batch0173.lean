import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1384 : RatBall :=
  ⟨⟨-51/320, -111/320⟩, 3/640⟩
def center1384 : GaussianRat :=
  ⟨-124318847/1000000000, -121658863/500000000⟩
def contact1384 : RatBall := localContactBall tau1384 center1384
def work1384 : RoundedTauEval :=
  evalTau precision tau1384 contact1384 logTwoBall

theorem center_sq1384 : (center1384.re : ℝ)^2 +
    (center1384.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1384]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1384 : work1384.theta.ok = true ∧
    work1384.jac.invOK = true ∧ acceptsUnitSq work1384.out = true := by
  norm_num [work1384, contact1384, tau1384, center1384, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1384 : CellCertificate where
  tauBall := tau1384
  contactCenter := center1384
  contactBall := contact1384
  work := work1384
  center_sq := center_sq1384
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1384.1
  jac_ok := checks1384.2.1
  accepted := checks1384.2.2

def tau1385 : RatBall :=
  ⟨⟨-49/320, -111/320⟩, 3/640⟩
def center1385 : GaussianRat :=
  ⟨-29895113/250000000, -121954461/500000000⟩
def contact1385 : RatBall := localContactBall tau1385 center1385
def work1385 : RoundedTauEval :=
  evalTau precision tau1385 contact1385 logTwoBall

theorem center_sq1385 : (center1385.re : ℝ)^2 +
    (center1385.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1385]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1385 : work1385.theta.ok = true ∧
    work1385.jac.invOK = true ∧ acceptsUnitSq work1385.out = true := by
  norm_num [work1385, contact1385, tau1385, center1385, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1385 : CellCertificate where
  tauBall := tau1385
  contactCenter := center1385
  contactBall := contact1385
  work := work1385
  center_sq := center_sq1385
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1385.1
  jac_ok := checks1385.2.1
  accepted := checks1385.2.2

def tau1386 : RatBall :=
  ⟨⟨-51/320, -109/320⟩, 3/640⟩
def center1386 : GaussianRat :=
  ⟨-61862799/500000000, -238597409/1000000000⟩
def contact1386 : RatBall := localContactBall tau1386 center1386
def work1386 : RoundedTauEval :=
  evalTau precision tau1386 contact1386 logTwoBall

theorem center_sq1386 : (center1386.re : ℝ)^2 +
    (center1386.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1386]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1386 : work1386.theta.ok = true ∧
    work1386.jac.invOK = true ∧ acceptsUnitSq work1386.out = true := by
  norm_num [work1386, contact1386, tau1386, center1386, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1386 : CellCertificate where
  tauBall := tau1386
  contactCenter := center1386
  contactBall := contact1386
  work := work1386
  center_sq := center_sq1386
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1386.1
  jac_ok := checks1386.2.1
  accepted := checks1386.2.2

def tau1387 : RatBall :=
  ⟨⟨-49/320, -109/320⟩, 3/640⟩
def center1387 : GaussianRat :=
  ⟨-119007309/1000000000, -59793181/250000000⟩
def contact1387 : RatBall := localContactBall tau1387 center1387
def work1387 : RoundedTauEval :=
  evalTau precision tau1387 contact1387 logTwoBall

theorem center_sq1387 : (center1387.re : ℝ)^2 +
    (center1387.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1387]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1387 : work1387.theta.ok = true ∧
    work1387.jac.invOK = true ∧ acceptsUnitSq work1387.out = true := by
  norm_num [work1387, contact1387, tau1387, center1387, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1387 : CellCertificate where
  tauBall := tau1387
  contactCenter := center1387
  contactBall := contact1387
  work := work1387
  center_sq := center_sq1387
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1387.1
  jac_ok := checks1387.2.1
  accepted := checks1387.2.2

def tau1388 : RatBall :=
  ⟨⟨-11/64, -107/320⟩, 3/640⟩
def center1388 : GaussianRat :=
  ⟨-66249189/500000000, -232719989/1000000000⟩
def contact1388 : RatBall := localContactBall tau1388 center1388
def work1388 : RoundedTauEval :=
  evalTau precision tau1388 contact1388 logTwoBall

theorem center_sq1388 : (center1388.re : ℝ)^2 +
    (center1388.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1388]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1388 : work1388.theta.ok = true ∧
    work1388.jac.invOK = true ∧ acceptsUnitSq work1388.out = true := by
  norm_num [work1388, contact1388, tau1388, center1388, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1388 : CellCertificate where
  tauBall := tau1388
  contactCenter := center1388
  contactBall := contact1388
  work := work1388
  center_sq := center_sq1388
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1388.1
  jac_ok := checks1388.2.1
  accepted := checks1388.2.2

def tau1389 : RatBall :=
  ⟨⟨-53/320, -107/320⟩, 3/640⟩
def center1389 : GaussianRat :=
  ⟨-15978923/125000000, -233317801/1000000000⟩
def contact1389 : RatBall := localContactBall tau1389 center1389
def work1389 : RoundedTauEval :=
  evalTau precision tau1389 contact1389 logTwoBall

theorem center_sq1389 : (center1389.re : ℝ)^2 +
    (center1389.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1389]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1389 : work1389.theta.ok = true ∧
    work1389.jac.invOK = true ∧ acceptsUnitSq work1389.out = true := by
  norm_num [work1389, contact1389, tau1389, center1389, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1389 : CellCertificate where
  tauBall := tau1389
  contactCenter := center1389
  contactBall := contact1389
  work := work1389
  center_sq := center_sq1389
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1389.1
  jac_ok := checks1389.2.1
  accepted := checks1389.2.2

def tau1390 : RatBall :=
  ⟨⟨-11/64, -21/64⟩, 3/640⟩
def center1390 : GaussianRat :=
  ⟨-65949739/500000000, -57017591/250000000⟩
def contact1390 : RatBall := localContactBall tau1390 center1390
def work1390 : RoundedTauEval :=
  evalTau precision tau1390 contact1390 logTwoBall

theorem center_sq1390 : (center1390.re : ℝ)^2 +
    (center1390.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1390]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1390 : work1390.theta.ok = true ∧
    work1390.jac.invOK = true ∧ acceptsUnitSq work1390.out = true := by
  norm_num [work1390, contact1390, tau1390, center1390, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1390 : CellCertificate where
  tauBall := tau1390
  contactCenter := center1390
  contactBall := contact1390
  work := work1390
  center_sq := center_sq1390
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1390.1
  jac_ok := checks1390.2.1
  accepted := checks1390.2.2

def tau1391 : RatBall :=
  ⟨⟨-53/320, -21/64⟩, 3/640⟩
def center1391 : GaussianRat :=
  ⟨-127250921/1000000000, -228652029/1000000000⟩
def contact1391 : RatBall := localContactBall tau1391 center1391
def work1391 : RoundedTauEval :=
  evalTau precision tau1391 contact1391 logTwoBall

theorem center_sq1391 : (center1391.re : ℝ)^2 +
    (center1391.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1391]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1391 : work1391.theta.ok = true ∧
    work1391.jac.invOK = true ∧ acceptsUnitSq work1391.out = true := by
  norm_num [work1391, contact1391, tau1391, center1391, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1391 : CellCertificate where
  tauBall := tau1391
  contactCenter := center1391
  contactBall := contact1391
  work := work1391
  center_sq := center_sq1391
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1391.1
  jac_ok := checks1391.2.1
  accepted := checks1391.2.2

def cells : List CellCertificate := [cell1384, cell1385, cell1386, cell1387, cell1388, cell1389, cell1390, cell1391]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173
