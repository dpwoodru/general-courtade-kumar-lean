import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1424 : RatBall :=
  ⟨⟨-43/320, -111/320⟩, 3/640⟩
def center1424 : GaussianRat :=
  ⟨-21054511/200000000, -122778933/500000000⟩
def contact1424 : RatBall := localContactBall tau1424 center1424
def work1424 : RoundedTauEval :=
  evalTau precision tau1424 contact1424 logTwoBall

theorem center_sq1424 : (center1424.re : ℝ)^2 +
    (center1424.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1424]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1424 : work1424.theta.ok = true ∧
    work1424.jac.invOK = true ∧ acceptsUnitSq work1424.out = true := by
  norm_num [work1424, contact1424, tau1424, center1424, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1424 : CellCertificate where
  tauBall := tau1424
  contactCenter := center1424
  contactBall := contact1424
  work := work1424
  center_sq := center_sq1424
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1424.1
  jac_ok := checks1424.2.1
  accepted := checks1424.2.2

def tau1425 : RatBall :=
  ⟨⟨-41/320, -111/320⟩, 3/640⟩
def center1425 : GaussianRat :=
  ⟨-100474143/1000000000, -123032409/500000000⟩
def contact1425 : RatBall := localContactBall tau1425 center1425
def work1425 : RoundedTauEval :=
  evalTau precision tau1425 contact1425 logTwoBall

theorem center_sq1425 : (center1425.re : ℝ)^2 +
    (center1425.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1425]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1425 : work1425.theta.ok = true ∧
    work1425.jac.invOK = true ∧ acceptsUnitSq work1425.out = true := by
  norm_num [work1425, contact1425, tau1425, center1425, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1425 : CellCertificate where
  tauBall := tau1425
  contactCenter := center1425
  contactBall := contact1425
  work := work1425
  center_sq := center_sq1425
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1425.1
  jac_ok := checks1425.2.1
  accepted := checks1425.2.2

def tau1426 : RatBall :=
  ⟨⟨-43/320, -109/320⟩, 3/640⟩
def center1426 : GaussianRat :=
  ⟨-26190451/250000000, -3762143/15625000⟩
def contact1426 : RatBall := localContactBall tau1426 center1426
def work1426 : RoundedTauEval :=
  evalTau precision tau1426 contact1426 logTwoBall

theorem center_sq1426 : (center1426.re : ℝ)^2 +
    (center1426.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1426]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1426 : work1426.theta.ok = true ∧
    work1426.jac.invOK = true ∧ acceptsUnitSq work1426.out = true := by
  norm_num [work1426, contact1426, tau1426, center1426, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1426 : CellCertificate where
  tauBall := tau1426
  contactCenter := center1426
  contactBall := contact1426
  work := work1426
  center_sq := center_sq1426
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1426.1
  jac_ok := checks1426.2.1
  accepted := checks1426.2.2

def tau1427 : RatBall :=
  ⟨⟨-41/320, -109/320⟩, 3/640⟩
def center1427 : GaussianRat :=
  ⟨-6249053/62500000, -241270351/1000000000⟩
def contact1427 : RatBall := localContactBall tau1427 center1427
def work1427 : RoundedTauEval :=
  evalTau precision tau1427 contact1427 logTwoBall

theorem center_sq1427 : (center1427.re : ℝ)^2 +
    (center1427.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1427]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1427 : work1427.theta.ok = true ∧
    work1427.jac.invOK = true ∧ acceptsUnitSq work1427.out = true := by
  norm_num [work1427, contact1427, tau1427, center1427, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1427 : CellCertificate where
  tauBall := tau1427
  contactCenter := center1427
  contactBall := contact1427
  work := work1427
  center_sq := center_sq1427
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1427.1
  jac_ok := checks1427.2.1
  accepted := checks1427.2.2

def tau1428 : RatBall :=
  ⟨⟨-47/320, -107/320⟩, 3/640⟩
def center1428 : GaussianRat :=
  ⟨-56867911/500000000, -234996813/1000000000⟩
def contact1428 : RatBall := localContactBall tau1428 center1428
def work1428 : RoundedTauEval :=
  evalTau precision tau1428 contact1428 logTwoBall

theorem center_sq1428 : (center1428.re : ℝ)^2 +
    (center1428.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1428]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1428 : work1428.theta.ok = true ∧
    work1428.jac.invOK = true ∧ acceptsUnitSq work1428.out = true := by
  norm_num [work1428, contact1428, tau1428, center1428, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1428 : CellCertificate where
  tauBall := tau1428
  contactCenter := center1428
  contactBall := contact1428
  work := work1428
  center_sq := center_sq1428
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1428.1
  jac_ok := checks1428.2.1
  accepted := checks1428.2.2

def tau1429 : RatBall :=
  ⟨⟨-9/64, -107/320⟩, 3/640⟩
def center1429 : GaussianRat :=
  ⟨-109007417/1000000000, -235517221/1000000000⟩
def contact1429 : RatBall := localContactBall tau1429 center1429
def work1429 : RoundedTauEval :=
  evalTau precision tau1429 contact1429 logTwoBall

theorem center_sq1429 : (center1429.re : ℝ)^2 +
    (center1429.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1429]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1429 : work1429.theta.ok = true ∧
    work1429.jac.invOK = true ∧ acceptsUnitSq work1429.out = true := by
  norm_num [work1429, contact1429, tau1429, center1429, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1429 : CellCertificate where
  tauBall := tau1429
  contactCenter := center1429
  contactBall := contact1429
  work := work1429
  center_sq := center_sq1429
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1429.1
  jac_ok := checks1429.2.1
  accepted := checks1429.2.2

def tau1430 : RatBall :=
  ⟨⟨-47/320, -21/64⟩, 3/640⟩
def center1430 : GaussianRat :=
  ⟨-22642537/200000000, -230285467/1000000000⟩
def contact1430 : RatBall := localContactBall tau1430 center1430
def work1430 : RoundedTauEval :=
  evalTau precision tau1430 contact1430 logTwoBall

theorem center_sq1430 : (center1430.re : ℝ)^2 +
    (center1430.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1430]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1430 : work1430.theta.ok = true ∧
    work1430.jac.invOK = true ∧ acceptsUnitSq work1430.out = true := by
  norm_num [work1430, contact1430, tau1430, center1430, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1430 : CellCertificate where
  tauBall := tau1430
  contactCenter := center1430
  contactBall := contact1430
  work := work1430
  center_sq := center_sq1430
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1430.1
  jac_ok := checks1430.2.1
  accepted := checks1430.2.2

def tau1431 : RatBall :=
  ⟨⟨-9/64, -21/64⟩, 3/640⟩
def center1431 : GaussianRat :=
  ⟨-21700807/200000000, -115395841/500000000⟩
def contact1431 : RatBall := localContactBall tau1431 center1431
def work1431 : RoundedTauEval :=
  evalTau precision tau1431 contact1431 logTwoBall

theorem center_sq1431 : (center1431.re : ℝ)^2 +
    (center1431.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1431]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1431 : work1431.theta.ok = true ∧
    work1431.jac.invOK = true ∧ acceptsUnitSq work1431.out = true := by
  norm_num [work1431, contact1431, tau1431, center1431, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1431 : CellCertificate where
  tauBall := tau1431
  contactCenter := center1431
  contactBall := contact1431
  work := work1431
  center_sq := center_sq1431
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1431.1
  jac_ok := checks1431.2.1
  accepted := checks1431.2.2

def cells : List CellCertificate := [cell1424, cell1425, cell1426, cell1427, cell1428, cell1429, cell1430, cell1431]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178
