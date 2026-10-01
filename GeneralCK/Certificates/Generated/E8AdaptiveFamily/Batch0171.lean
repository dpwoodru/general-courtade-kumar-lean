import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1368 : RatBall :=
  ⟨⟨-59/320, -111/320⟩, 3/640⟩
def center1368 : GaussianRat :=
  ⟨-143104409/1000000000, -240754941/1000000000⟩
def contact1368 : RatBall := localContactBall tau1368 center1368
def work1368 : RoundedTauEval :=
  evalTau precision tau1368 contact1368 logTwoBall

theorem center_sq1368 : (center1368.re : ℝ)^2 +
    (center1368.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1368]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1368 : work1368.theta.ok = true ∧
    work1368.jac.invOK = true ∧ acceptsUnitSq work1368.out = true := by
  norm_num [work1368, contact1368, tau1368, center1368, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1368 : CellCertificate where
  tauBall := tau1368
  contactCenter := center1368
  contactBall := contact1368
  work := work1368
  center_sq := center_sq1368
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1368.1
  jac_ok := checks1368.2.1
  accepted := checks1368.2.2

def tau1369 : RatBall :=
  ⟨⟨-57/320, -111/320⟩, 3/640⟩
def center1369 : GaussianRat :=
  ⟨-138434183/1000000000, -120712289/500000000⟩
def contact1369 : RatBall := localContactBall tau1369 center1369
def work1369 : RoundedTauEval :=
  evalTau precision tau1369 contact1369 logTwoBall

theorem center_sq1369 : (center1369.re : ℝ)^2 +
    (center1369.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1369]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1369 : work1369.theta.ok = true ∧
    work1369.jac.invOK = true ∧ acceptsUnitSq work1369.out = true := by
  norm_num [work1369, contact1369, tau1369, center1369, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1369 : CellCertificate where
  tauBall := tau1369
  contactCenter := center1369
  contactBall := contact1369
  work := work1369
  center_sq := center_sq1369
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1369.1
  jac_ok := checks1369.2.1
  accepted := checks1369.2.2

def tau1370 : RatBall :=
  ⟨⟨-59/320, -109/320⟩, 3/640⟩
def center1370 : GaussianRat :=
  ⟨-71217211/500000000, -236102993/1000000000⟩
def contact1370 : RatBall := localContactBall tau1370 center1370
def work1370 : RoundedTauEval :=
  evalTau precision tau1370 contact1370 logTwoBall

theorem center_sq1370 : (center1370.re : ℝ)^2 +
    (center1370.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1370]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1370 : work1370.theta.ok = true ∧
    work1370.jac.invOK = true ∧ acceptsUnitSq work1370.out = true := by
  norm_num [work1370, contact1370, tau1370, center1370, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1370 : CellCertificate where
  tauBall := tau1370
  contactCenter := center1370
  contactBall := contact1370
  work := work1370
  center_sq := center_sq1370
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1370.1
  jac_ok := checks1370.2.1
  accepted := checks1370.2.2

def tau1371 : RatBall :=
  ⟨⟨-57/320, -109/320⟩, 3/640⟩
def center1371 : GaussianRat :=
  ⟨-137782813/1000000000, -5918871/25000000⟩
def contact1371 : RatBall := localContactBall tau1371 center1371
def work1371 : RoundedTauEval :=
  evalTau precision tau1371 contact1371 logTwoBall

theorem center_sq1371 : (center1371.re : ℝ)^2 +
    (center1371.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1371]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1371 : work1371.theta.ok = true ∧
    work1371.jac.invOK = true ∧ acceptsUnitSq work1371.out = true := by
  norm_num [work1371, contact1371, tau1371, center1371, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1371 : CellCertificate where
  tauBall := tau1371
  contactCenter := center1371
  contactBall := contact1371
  work := work1371
  center_sq := center_sq1371
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1371.1
  jac_ok := checks1371.2.1
  accepted := checks1371.2.2

def tau1372 : RatBall :=
  ⟨⟨-63/320, -107/320⟩, 3/640⟩
def center1372 : GaussianRat :=
  ⟨-150996377/1000000000, -230147447/1000000000⟩
def contact1372 : RatBall := localContactBall tau1372 center1372
def work1372 : RoundedTauEval :=
  evalTau precision tau1372 contact1372 logTwoBall

theorem center_sq1372 : (center1372.re : ℝ)^2 +
    (center1372.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1372]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1372 : work1372.theta.ok = true ∧
    work1372.jac.invOK = true ∧ acceptsUnitSq work1372.out = true := by
  norm_num [work1372, contact1372, tau1372, center1372, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1372 : CellCertificate where
  tauBall := tau1372
  contactCenter := center1372
  contactBall := contact1372
  work := work1372
  center_sq := center_sq1372
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1372.1
  jac_ok := checks1372.2.1
  accepted := checks1372.2.2

def tau1373 : RatBall :=
  ⟨⟨-61/320, -107/320⟩, 3/640⟩
def center1373 : GaussianRat :=
  ⟨-146398251/1000000000, -115408523/500000000⟩
def contact1373 : RatBall := localContactBall tau1373 center1373
def work1373 : RoundedTauEval :=
  evalTau precision tau1373 contact1373 logTwoBall

theorem center_sq1373 : (center1373.re : ℝ)^2 +
    (center1373.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1373]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1373 : work1373.theta.ok = true ∧
    work1373.jac.invOK = true ∧ acceptsUnitSq work1373.out = true := by
  norm_num [work1373, contact1373, tau1373, center1373, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1373 : CellCertificate where
  tauBall := tau1373
  contactCenter := center1373
  contactBall := contact1373
  work := work1373
  center_sq := center_sq1373
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1373.1
  jac_ok := checks1373.2.1
  accepted := checks1373.2.2

def tau1374 : RatBall :=
  ⟨⟨-63/320, -21/64⟩, 3/640⟩
def center1374 : GaussianRat :=
  ⟨-75163641/500000000, -225566837/1000000000⟩
def contact1374 : RatBall := localContactBall tau1374 center1374
def work1374 : RoundedTauEval :=
  evalTau precision tau1374 contact1374 logTwoBall

theorem center_sq1374 : (center1374.re : ℝ)^2 +
    (center1374.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1374]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1374 : work1374.theta.ok = true ∧
    work1374.jac.invOK = true ∧ acceptsUnitSq work1374.out = true := by
  norm_num [work1374, contact1374, tau1374, center1374, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1374 : CellCertificate where
  tauBall := tau1374
  contactCenter := center1374
  contactBall := contact1374
  work := work1374
  center_sq := center_sq1374
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1374.1
  jac_ok := checks1374.2.1
  accepted := checks1374.2.2

def tau1375 : RatBall :=
  ⟨⟨-61/320, -21/64⟩, 3/640⟩
def center1375 : GaussianRat :=
  ⟨-145746161/1000000000, -113109273/500000000⟩
def contact1375 : RatBall := localContactBall tau1375 center1375
def work1375 : RoundedTauEval :=
  evalTau precision tau1375 contact1375 logTwoBall

theorem center_sq1375 : (center1375.re : ℝ)^2 +
    (center1375.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1375]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1375 : work1375.theta.ok = true ∧
    work1375.jac.invOK = true ∧ acceptsUnitSq work1375.out = true := by
  norm_num [work1375, contact1375, tau1375, center1375, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1375 : CellCertificate where
  tauBall := tau1375
  contactCenter := center1375
  contactBall := contact1375
  work := work1375
  center_sq := center_sq1375
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1375.1
  jac_ok := checks1375.2.1
  accepted := checks1375.2.2

def cells : List CellCertificate := [cell1368, cell1369, cell1370, cell1371, cell1372, cell1373, cell1374, cell1375]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171
