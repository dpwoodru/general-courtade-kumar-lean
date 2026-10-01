import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0191

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1528 : RatBall :=
  ⟨⟨-31/320, -111/320⟩, 3/640⟩
def center1528 : GaussianRat :=
  ⟨-76289393/1000000000, -248265049/1000000000⟩
def contact1528 : RatBall := localContactBall tau1528 center1528
def work1528 : RoundedTauEval :=
  evalTau precision tau1528 contact1528 logTwoBall

theorem center_sq1528 : (center1528.re : ℝ)^2 +
    (center1528.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1528]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1528 : work1528.theta.ok = true ∧
    work1528.jac.invOK = true ∧ acceptsUnitSq work1528.out = true := by
  norm_num [work1528, contact1528, tau1528, center1528, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1528 : CellCertificate where
  tauBall := tau1528
  contactCenter := center1528
  contactBall := contact1528
  work := work1528
  center_sq := center_sq1528
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1528.1
  jac_ok := checks1528.2.1
  accepted := checks1528.2.2

def tau1529 : RatBall :=
  ⟨⟨-29/320, -111/320⟩, 3/640⟩
def center1529 : GaussianRat :=
  ⟨-7141811/100000000, -9945447/40000000⟩
def contact1529 : RatBall := localContactBall tau1529 center1529
def work1529 : RoundedTauEval :=
  evalTau precision tau1529 contact1529 logTwoBall

theorem center_sq1529 : (center1529.re : ℝ)^2 +
    (center1529.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1529]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1529 : work1529.theta.ok = true ∧
    work1529.jac.invOK = true ∧ acceptsUnitSq work1529.out = true := by
  norm_num [work1529, contact1529, tau1529, center1529, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1529 : CellCertificate where
  tauBall := tau1529
  contactCenter := center1529
  contactBall := contact1529
  work := work1529
  center_sq := center_sq1529
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1529.1
  jac_ok := checks1529.2.1
  accepted := checks1529.2.2

def tau1530 : RatBall :=
  ⟨⟨-31/320, -109/320⟩, 3/640⟩
def center1530 : GaussianRat :=
  ⟨-75911827/1000000000, -121705269/500000000⟩
def contact1530 : RatBall := localContactBall tau1530 center1530
def work1530 : RoundedTauEval :=
  evalTau precision tau1530 contact1530 logTwoBall

theorem center_sq1530 : (center1530.re : ℝ)^2 +
    (center1530.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1530]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1530 : work1530.theta.ok = true ∧
    work1530.jac.invOK = true ∧ acceptsUnitSq work1530.out = true := by
  norm_num [work1530, contact1530, tau1530, center1530, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1530 : CellCertificate where
  tauBall := tau1530
  contactCenter := center1530
  contactBall := contact1530
  work := work1530
  center_sq := center_sq1530
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1530.1
  jac_ok := checks1530.2.1
  accepted := checks1530.2.2

def tau1531 : RatBall :=
  ⟨⟨-29/320, -109/320⟩, 3/640⟩
def center1531 : GaussianRat :=
  ⟨-17765923/250000000, -243771477/1000000000⟩
def contact1531 : RatBall := localContactBall tau1531 center1531
def work1531 : RoundedTauEval :=
  evalTau precision tau1531 contact1531 logTwoBall

theorem center_sq1531 : (center1531.re : ℝ)^2 +
    (center1531.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1531]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1531 : work1531.theta.ok = true ∧
    work1531.jac.invOK = true ∧ acceptsUnitSq work1531.out = true := by
  norm_num [work1531, contact1531, tau1531, center1531, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1531 : CellCertificate where
  tauBall := tau1531
  contactCenter := center1531
  contactBall := contact1531
  work := work1531
  center_sq := center_sq1531
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1531.1
  jac_ok := checks1531.2.1
  accepted := checks1531.2.2

def tau1532 : RatBall :=
  ⟨⟨-27/320, -111/320⟩, 3/640⟩
def center1532 : GaussianRat :=
  ⟨-66536837/1000000000, -62245929/250000000⟩
def contact1532 : RatBall := localContactBall tau1532 center1532
def work1532 : RoundedTauEval :=
  evalTau precision tau1532 contact1532 logTwoBall

theorem center_sq1532 : (center1532.re : ℝ)^2 +
    (center1532.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1532]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1532 : work1532.theta.ok = true ∧
    work1532.jac.invOK = true ∧ acceptsUnitSq work1532.out = true := by
  norm_num [work1532, contact1532, tau1532, center1532, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1532 : CellCertificate where
  tauBall := tau1532
  contactCenter := center1532
  contactBall := contact1532
  work := work1532
  center_sq := center_sq1532
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1532.1
  jac_ok := checks1532.2.1
  accepted := checks1532.2.2

def tau1533 : RatBall :=
  ⟨⟨-5/64, -111/320⟩, 3/640⟩
def center1533 : GaussianRat :=
  ⟨-30823109/500000000, -249307439/1000000000⟩
def contact1533 : RatBall := localContactBall tau1533 center1533
def work1533 : RoundedTauEval :=
  evalTau precision tau1533 contact1533 logTwoBall

theorem center_sq1533 : (center1533.re : ℝ)^2 +
    (center1533.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1533]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1533 : work1533.theta.ok = true ∧
    work1533.jac.invOK = true ∧ acceptsUnitSq work1533.out = true := by
  norm_num [work1533, contact1533, tau1533, center1533, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1533 : CellCertificate where
  tauBall := tau1533
  contactCenter := center1533
  contactBall := contact1533
  work := work1533
  center_sq := center_sq1533
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1533.1
  jac_ok := checks1533.2.1
  accepted := checks1533.2.2

def tau1534 : RatBall :=
  ⟨⟨-27/320, -109/320⟩, 3/640⟩
def center1534 : GaussianRat :=
  ⟨-16551451/250000000, -30513683/125000000⟩
def contact1534 : RatBall := localContactBall tau1534 center1534
def work1534 : RoundedTauEval :=
  evalTau precision tau1534 contact1534 logTwoBall

theorem center_sq1534 : (center1534.re : ℝ)^2 +
    (center1534.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1534]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1534 : work1534.theta.ok = true ∧
    work1534.jac.invOK = true ∧ acceptsUnitSq work1534.out = true := by
  norm_num [work1534, contact1534, tau1534, center1534, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1534 : CellCertificate where
  tauBall := tau1534
  contactCenter := center1534
  contactBall := contact1534
  work := work1534
  center_sq := center_sq1534
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1534.1
  jac_ok := checks1534.2.1
  accepted := checks1534.2.2

def tau1535 : RatBall :=
  ⟨⟨-5/64, -109/320⟩, 3/640⟩
def center1535 : GaussianRat :=
  ⟨-6133879/100000000, -244424273/1000000000⟩
def contact1535 : RatBall := localContactBall tau1535 center1535
def work1535 : RoundedTauEval :=
  evalTau precision tau1535 contact1535 logTwoBall

theorem center_sq1535 : (center1535.re : ℝ)^2 +
    (center1535.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1535]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1535 : work1535.theta.ok = true ∧
    work1535.jac.invOK = true ∧ acceptsUnitSq work1535.out = true := by
  norm_num [work1535, contact1535, tau1535, center1535, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1535 : CellCertificate where
  tauBall := tau1535
  contactCenter := center1535
  contactBall := contact1535
  work := work1535
  center_sq := center_sq1535
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1535.1
  jac_ok := checks1535.2.1
  accepted := checks1535.2.2

def cells : List CellCertificate := [cell1528, cell1529, cell1530, cell1531, cell1532, cell1533, cell1534, cell1535]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0191
