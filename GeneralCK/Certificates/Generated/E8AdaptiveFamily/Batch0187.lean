import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1496 : RatBall :=
  ⟨⟨-3/320, -123/320⟩, 3/640⟩
def center1496 : GaussianRat :=
  ⟨-3836831/500000000, -281424629/1000000000⟩
def contact1496 : RatBall := localContactBall tau1496 center1496
def work1496 : RoundedTauEval :=
  evalTau precision tau1496 contact1496 logTwoBall

theorem center_sq1496 : (center1496.re : ℝ)^2 +
    (center1496.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1496]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1496 : work1496.theta.ok = true ∧
    work1496.jac.invOK = true ∧ acceptsUnitSq work1496.out = true := by
  norm_num [work1496, contact1496, tau1496, center1496, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1496 : CellCertificate where
  tauBall := tau1496
  contactCenter := center1496
  contactBall := contact1496
  work := work1496
  center_sq := center_sq1496
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1496.1
  jac_ok := checks1496.2.1
  accepted := checks1496.2.2

def tau1497 : RatBall :=
  ⟨⟨-1/320, -123/320⟩, 3/640⟩
def center1497 : GaussianRat :=
  ⟨-2558027/1000000000, -14072733/50000000⟩
def contact1497 : RatBall := localContactBall tau1497 center1497
def work1497 : RoundedTauEval :=
  evalTau precision tau1497 contact1497 logTwoBall

theorem center_sq1497 : (center1497.re : ℝ)^2 +
    (center1497.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1497]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1497 : work1497.theta.ok = true ∧
    work1497.jac.invOK = true ∧ acceptsUnitSq work1497.out = true := by
  norm_num [work1497, contact1497, tau1497, center1497, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1497 : CellCertificate where
  tauBall := tau1497
  contactCenter := center1497
  contactBall := contact1497
  work := work1497
  center_sq := center_sq1497
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1497.1
  jac_ok := checks1497.2.1
  accepted := checks1497.2.2

def tau1498 : RatBall :=
  ⟨⟨-3/320, -121/320⟩, 3/640⟩
def center1498 : GaussianRat :=
  ⟨-1907311/250000000, -69081087/250000000⟩
def contact1498 : RatBall := localContactBall tau1498 center1498
def work1498 : RoundedTauEval :=
  evalTau precision tau1498 contact1498 logTwoBall

theorem center_sq1498 : (center1498.re : ℝ)^2 +
    (center1498.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1498]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1498 : work1498.theta.ok = true ∧
    work1498.jac.invOK = true ∧ acceptsUnitSq work1498.out = true := by
  norm_num [work1498, contact1498, tau1498, center1498, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1498 : CellCertificate where
  tauBall := tau1498
  contactCenter := center1498
  contactBall := contact1498
  work := work1498
  center_sq := center_sq1498
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1498.1
  jac_ok := checks1498.2.1
  accepted := checks1498.2.2

def tau1499 : RatBall :=
  ⟨⟨-1/320, -121/320⟩, 3/640⟩
def center1499 : GaussianRat :=
  ⟨-2543217/1000000000, -276353553/1000000000⟩
def contact1499 : RatBall := localContactBall tau1499 center1499
def work1499 : RoundedTauEval :=
  evalTau precision tau1499 contact1499 logTwoBall

theorem center_sq1499 : (center1499.re : ℝ)^2 +
    (center1499.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1499]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1499 : work1499.theta.ok = true ∧
    work1499.jac.invOK = true ∧ acceptsUnitSq work1499.out = true := by
  norm_num [work1499, contact1499, tau1499, center1499, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1499 : CellCertificate where
  tauBall := tau1499
  contactCenter := center1499
  contactBall := contact1499
  work := work1499
  center_sq := center_sq1499
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1499.1
  jac_ok := checks1499.2.1
  accepted := checks1499.2.2

def tau1500 : RatBall :=
  ⟨⟨-3/64, -119/320⟩, 3/640⟩
def center1500 : GaussianRat :=
  ⟨-18938457/500000000, -5409781/20000000⟩
def contact1500 : RatBall := localContactBall tau1500 center1500
def work1500 : RoundedTauEval :=
  evalTau precision tau1500 contact1500 logTwoBall

theorem center_sq1500 : (center1500.re : ℝ)^2 +
    (center1500.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1500]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1500 : work1500.theta.ok = true ∧
    work1500.jac.invOK = true ∧ acceptsUnitSq work1500.out = true := by
  norm_num [work1500, contact1500, tau1500, center1500, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1500 : CellCertificate where
  tauBall := tau1500
  contactCenter := center1500
  contactBall := contact1500
  work := work1500
  center_sq := center_sq1500
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1500.1
  jac_ok := checks1500.2.1
  accepted := checks1500.2.2

def tau1501 : RatBall :=
  ⟨⟨-13/320, -119/320⟩, 3/640⟩
def center1501 : GaussianRat :=
  ⟨-32838611/1000000000, -135343343/500000000⟩
def contact1501 : RatBall := localContactBall tau1501 center1501
def work1501 : RoundedTauEval :=
  evalTau precision tau1501 contact1501 logTwoBall

theorem center_sq1501 : (center1501.re : ℝ)^2 +
    (center1501.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1501]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1501 : work1501.theta.ok = true ∧
    work1501.jac.invOK = true ∧ acceptsUnitSq work1501.out = true := by
  norm_num [work1501, contact1501, tau1501, center1501, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1501 : CellCertificate where
  tauBall := tau1501
  contactCenter := center1501
  contactBall := contact1501
  work := work1501
  center_sq := center_sq1501
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1501.1
  jac_ok := checks1501.2.1
  accepted := checks1501.2.2

def tau1502 : RatBall :=
  ⟨⟨-3/64, -117/320⟩, 3/640⟩
def center1502 : GaussianRat :=
  ⟨-18834129/500000000, -13273367/50000000⟩
def contact1502 : RatBall := localContactBall tau1502 center1502
def work1502 : RoundedTauEval :=
  evalTau precision tau1502 contact1502 logTwoBall

theorem center_sq1502 : (center1502.re : ℝ)^2 +
    (center1502.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1502]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1502 : work1502.theta.ok = true ∧
    work1502.jac.invOK = true ∧ acceptsUnitSq work1502.out = true := by
  norm_num [work1502, contact1502, tau1502, center1502, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1502 : CellCertificate where
  tauBall := tau1502
  contactCenter := center1502
  contactBall := contact1502
  work := work1502
  center_sq := center_sq1502
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1502.1
  jac_ok := checks1502.2.1
  accepted := checks1502.2.2

def tau1503 : RatBall :=
  ⟨⟨-13/320, -117/320⟩, 3/640⟩
def center1503 : GaussianRat :=
  ⟨-6531493/200000000, -265659553/1000000000⟩
def contact1503 : RatBall := localContactBall tau1503 center1503
def work1503 : RoundedTauEval :=
  evalTau precision tau1503 contact1503 logTwoBall

theorem center_sq1503 : (center1503.re : ℝ)^2 +
    (center1503.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1503]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1503 : work1503.theta.ok = true ∧
    work1503.jac.invOK = true ∧ acceptsUnitSq work1503.out = true := by
  norm_num [work1503, contact1503, tau1503, center1503, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1503 : CellCertificate where
  tauBall := tau1503
  contactCenter := center1503
  contactBall := contact1503
  work := work1503
  center_sq := center_sq1503
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1503.1
  jac_ok := checks1503.2.1
  accepted := checks1503.2.2

def cells : List CellCertificate := [cell1496, cell1497, cell1498, cell1499, cell1500, cell1501, cell1502, cell1503]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187
