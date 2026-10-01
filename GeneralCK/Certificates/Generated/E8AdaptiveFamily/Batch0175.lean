import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1400 : RatBall :=
  ⟨⟨-59/320, -103/320⟩, 3/640⟩
def center1400 : GaussianRat :=
  ⟨-140529903/1000000000, -222254637/1000000000⟩
def contact1400 : RatBall := localContactBall tau1400 center1400
def work1400 : RoundedTauEval :=
  evalTau precision tau1400 contact1400 logTwoBall

theorem center_sq1400 : (center1400.re : ℝ)^2 +
    (center1400.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1400]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1400 : work1400.theta.ok = true ∧
    work1400.jac.invOK = true ∧ acceptsUnitSq work1400.out = true := by
  norm_num [work1400, contact1400, tau1400, center1400, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1400 : CellCertificate where
  tauBall := tau1400
  contactCenter := center1400
  contactBall := contact1400
  work := work1400
  center_sq := center_sq1400
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1400.1
  jac_ok := checks1400.2.1
  accepted := checks1400.2.2

def tau1401 : RatBall :=
  ⟨⟨-57/320, -103/320⟩, 3/640⟩
def center1401 : GaussianRat :=
  ⟨-135931497/1000000000, -55713833/250000000⟩
def contact1401 : RatBall := localContactBall tau1401 center1401
def work1401 : RoundedTauEval :=
  evalTau precision tau1401 contact1401 logTwoBall

theorem center_sq1401 : (center1401.re : ℝ)^2 +
    (center1401.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1401]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1401 : work1401.theta.ok = true ∧
    work1401.jac.invOK = true ∧ acceptsUnitSq work1401.out = true := by
  norm_num [work1401, contact1401, tau1401, center1401, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1401 : CellCertificate where
  tauBall := tau1401
  contactCenter := center1401
  contactBall := contact1401
  work := work1401
  center_sq := center_sq1401
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1401.1
  jac_ok := checks1401.2.1
  accepted := checks1401.2.2

def tau1402 : RatBall :=
  ⟨⟨-59/320, -101/320⟩, 3/640⟩
def center1402 : GaussianRat :=
  ⟨-27985801/200000000, -54418229/250000000⟩
def contact1402 : RatBall := localContactBall tau1402 center1402
def work1402 : RoundedTauEval :=
  evalTau precision tau1402 contact1402 logTwoBall

theorem center_sq1402 : (center1402.re : ℝ)^2 +
    (center1402.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1402]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1402 : work1402.theta.ok = true ∧
    work1402.jac.invOK = true ∧ acceptsUnitSq work1402.out = true := by
  norm_num [work1402, contact1402, tau1402, center1402, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1402 : CellCertificate where
  tauBall := tau1402
  contactCenter := center1402
  contactBall := contact1402
  work := work1402
  center_sq := center_sq1402
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1402.1
  jac_ok := checks1402.2.1
  accepted := checks1402.2.2

def tau1403 : RatBall :=
  ⟨⟨-57/320, -101/320⟩, 3/640⟩
def center1403 : GaussianRat :=
  ⟨-135347471/1000000000, -43651451/200000000⟩
def contact1403 : RatBall := localContactBall tau1403 center1403
def work1403 : RoundedTauEval :=
  evalTau precision tau1403 contact1403 logTwoBall

theorem center_sq1403 : (center1403.re : ℝ)^2 +
    (center1403.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1403]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1403 : work1403.theta.ok = true ∧
    work1403.jac.invOK = true ∧ acceptsUnitSq work1403.out = true := by
  norm_num [work1403, contact1403, tau1403, center1403, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1403 : CellCertificate where
  tauBall := tau1403
  contactCenter := center1403
  contactBall := contact1403
  work := work1403
  center_sq := center_sq1403
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1403.1
  jac_ok := checks1403.2.1
  accepted := checks1403.2.2

def tau1404 : RatBall :=
  ⟨⟨-63/320, -99/320⟩, 3/640⟩
def center1404 : GaussianRat :=
  ⟨-148426041/1000000000, -105961569/500000000⟩
def contact1404 : RatBall := localContactBall tau1404 center1404
def work1404 : RoundedTauEval :=
  evalTau precision tau1404 contact1404 logTwoBall

theorem center_sq1404 : (center1404.re : ℝ)^2 +
    (center1404.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1404]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1404 : work1404.theta.ok = true ∧
    work1404.jac.invOK = true ∧ acceptsUnitSq work1404.out = true := by
  norm_num [work1404, contact1404, tau1404, center1404, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1404 : CellCertificate where
  tauBall := tau1404
  contactCenter := center1404
  contactBall := contact1404
  work := work1404
  center_sq := center_sq1404
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1404.1
  jac_ok := checks1404.2.1
  accepted := checks1404.2.2

def tau1405 : RatBall :=
  ⟨⟨-61/320, -99/320⟩, 3/640⟩
def center1405 : GaussianRat :=
  ⟨-28778703/200000000, -106261649/500000000⟩
def contact1405 : RatBall := localContactBall tau1405 center1405
def work1405 : RoundedTauEval :=
  evalTau precision tau1405 contact1405 logTwoBall

theorem center_sq1405 : (center1405.re : ℝ)^2 +
    (center1405.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1405]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1405 : work1405.theta.ok = true ∧
    work1405.jac.invOK = true ∧ acceptsUnitSq work1405.out = true := by
  norm_num [work1405, contact1405, tau1405, center1405, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1405 : CellCertificate where
  tauBall := tau1405
  contactCenter := center1405
  contactBall := contact1405
  work := work1405
  center_sq := center_sq1405
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1405.1
  jac_ok := checks1405.2.1
  accepted := checks1405.2.2

def tau1406 : RatBall :=
  ⟨⟨-63/320, -97/320⟩, 3/640⟩
def center1406 : GaussianRat :=
  ⟨-147826489/1000000000, -2592583/12500000⟩
def contact1406 : RatBall := localContactBall tau1406 center1406
def work1406 : RoundedTauEval :=
  evalTau precision tau1406 contact1406 logTwoBall

theorem center_sq1406 : (center1406.re : ℝ)^2 +
    (center1406.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1406]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1406 : work1406.theta.ok = true ∧
    work1406.jac.invOK = true ∧ acceptsUnitSq work1406.out = true := by
  norm_num [work1406, contact1406, tau1406, center1406, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1406 : CellCertificate where
  tauBall := tau1406
  contactCenter := center1406
  contactBall := contact1406
  work := work1406
  center_sq := center_sq1406
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1406.1
  jac_ok := checks1406.2.1
  accepted := checks1406.2.2

def tau1407 : RatBall :=
  ⟨⟨-61/320, -97/320⟩, 3/640⟩
def center1407 : GaussianRat :=
  ⟨-143309371/1000000000, -103995141/500000000⟩
def contact1407 : RatBall := localContactBall tau1407 center1407
def work1407 : RoundedTauEval :=
  evalTau precision tau1407 contact1407 logTwoBall

theorem center_sq1407 : (center1407.re : ℝ)^2 +
    (center1407.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1407]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1407 : work1407.theta.ok = true ∧
    work1407.jac.invOK = true ∧ acceptsUnitSq work1407.out = true := by
  norm_num [work1407, contact1407, tau1407, center1407, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1407 : CellCertificate where
  tauBall := tau1407
  contactCenter := center1407
  contactBall := contact1407
  work := work1407
  center_sq := center_sq1407
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1407.1
  jac_ok := checks1407.2.1
  accepted := checks1407.2.2

def cells : List CellCertificate := [cell1400, cell1401, cell1402, cell1403, cell1404, cell1405, cell1406, cell1407]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175
