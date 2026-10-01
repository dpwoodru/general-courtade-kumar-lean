import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0306

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2448 : RatBall :=
  ⟨⟨81/320, 17/64⟩, 3/640⟩
def center2448 : GaussianRat :=
  ⟨36750261/200000000, 1756473/10000000⟩
def contact2448 : RatBall := localContactBall tau2448 center2448
def work2448 : RoundedTauEval :=
  evalTau precision tau2448 contact2448 logTwoBall

theorem center_sq2448 : (center2448.re : ℝ)^2 +
    (center2448.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2448]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2448 : work2448.theta.ok = true ∧
    work2448.jac.invOK = true ∧ acceptsUnitSq work2448.out = true := by
  norm_num [work2448, contact2448, tau2448, center2448, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2448 : CellCertificate where
  tauBall := tau2448
  contactCenter := center2448
  contactBall := contact2448
  work := work2448
  center_sq := center_sq2448
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2448.1
  jac_ok := checks2448.2.1
  accepted := checks2448.2.2

def tau2449 : RatBall :=
  ⟨⟨83/320, 17/64⟩, 3/640⟩
def center2449 : GaussianRat :=
  ⟨188020707/1000000000, 4375997/25000000⟩
def contact2449 : RatBall := localContactBall tau2449 center2449
def work2449 : RoundedTauEval :=
  evalTau precision tau2449 contact2449 logTwoBall

theorem center_sq2449 : (center2449.re : ℝ)^2 +
    (center2449.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2449]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2449 : work2449.theta.ok = true ∧
    work2449.jac.invOK = true ∧ acceptsUnitSq work2449.out = true := by
  norm_num [work2449, contact2449, tau2449, center2449, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2449 : CellCertificate where
  tauBall := tau2449
  contactCenter := center2449
  contactBall := contact2449
  work := work2449
  center_sq := center_sq2449
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2449.1
  jac_ok := checks2449.2.1
  accepted := checks2449.2.2

def tau2450 : RatBall :=
  ⟨⟨81/320, 87/320⟩, 3/640⟩
def center2450 : GaussianRat :=
  ⟨9218121/50000000, 179930859/1000000000⟩
def contact2450 : RatBall := localContactBall tau2450 center2450
def work2450 : RoundedTauEval :=
  evalTau precision tau2450 contact2450 logTwoBall

theorem center_sq2450 : (center2450.re : ℝ)^2 +
    (center2450.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2450]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2450 : work2450.theta.ok = true ∧
    work2450.jac.invOK = true ∧ acceptsUnitSq work2450.out = true := by
  norm_num [work2450, contact2450, tau2450, center2450, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2450 : CellCertificate where
  tauBall := tau2450
  contactCenter := center2450
  contactBall := contact2450
  work := work2450
  center_sq := center_sq2450
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2450.1
  jac_ok := checks2450.2.1
  accepted := checks2450.2.2

def tau2451 : RatBall :=
  ⟨⟨83/320, 87/320⟩, 3/640⟩
def center2451 : GaussianRat :=
  ⟨188642281/1000000000, 22413187/125000000⟩
def contact2451 : RatBall := localContactBall tau2451 center2451
def work2451 : RoundedTauEval :=
  evalTau precision tau2451 contact2451 logTwoBall

theorem center_sq2451 : (center2451.re : ℝ)^2 +
    (center2451.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2451]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2451 : work2451.theta.ok = true ∧
    work2451.jac.invOK = true ∧ acceptsUnitSq work2451.out = true := by
  norm_num [work2451, contact2451, tau2451, center2451, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2451 : CellCertificate where
  tauBall := tau2451
  contactCenter := center2451
  contactBall := contact2451
  work := work2451
  center_sq := center_sq2451
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2451.1
  jac_ok := checks2451.2.1
  accepted := checks2451.2.2

def tau2452 : RatBall :=
  ⟨⟨17/64, 17/64⟩, 3/640⟩
def center2452 : GaussianRat :=
  ⟨12017011/62500000, 17442227/100000000⟩
def contact2452 : RatBall := localContactBall tau2452 center2452
def work2452 : RoundedTauEval :=
  evalTau precision tau2452 contact2452 logTwoBall

theorem center_sq2452 : (center2452.re : ℝ)^2 +
    (center2452.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2452]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2452 : work2452.theta.ok = true ∧
    work2452.jac.invOK = true ∧ acceptsUnitSq work2452.out = true := by
  norm_num [work2452, contact2452, tau2452, center2452, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2452 : CellCertificate where
  tauBall := tau2452
  contactCenter := center2452
  contactBall := contact2452
  work := work2452
  center_sq := center_sq2452
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2452.1
  jac_ok := checks2452.2.1
  accepted := checks2452.2.2

def tau2453 : RatBall :=
  ⟨⟨87/320, 17/64⟩, 3/640⟩
def center2453 : GaussianRat :=
  ⟨98252729/500000000, 34758949/200000000⟩
def contact2453 : RatBall := localContactBall tau2453 center2453
def work2453 : RoundedTauEval :=
  evalTau precision tau2453 contact2453 logTwoBall

theorem center_sq2453 : (center2453.re : ℝ)^2 +
    (center2453.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2453]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2453 : work2453.theta.ok = true ∧
    work2453.jac.invOK = true ∧ acceptsUnitSq work2453.out = true := by
  norm_num [work2453, contact2453, tau2453, center2453, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2453 : CellCertificate where
  tauBall := tau2453
  contactCenter := center2453
  contactBall := contact2453
  work := work2453
  center_sq := center_sq2453
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2453.1
  jac_ok := checks2453.2.1
  accepted := checks2453.2.2

def tau2454 : RatBall :=
  ⟨⟨17/64, 87/320⟩, 3/640⟩
def center2454 : GaussianRat :=
  ⟨192903929/1000000000, 35733937/200000000⟩
def contact2454 : RatBall := localContactBall tau2454 center2454
def work2454 : RoundedTauEval :=
  evalTau precision tau2454 contact2454 logTwoBall

theorem center_sq2454 : (center2454.re : ℝ)^2 +
    (center2454.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2454]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2454 : work2454.theta.ok = true ∧
    work2454.jac.invOK = true ∧ acceptsUnitSq work2454.out = true := by
  norm_num [work2454, contact2454, tau2454, center2454, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2454 : CellCertificate where
  tauBall := tau2454
  contactCenter := center2454
  contactBall := contact2454
  work := work2454
  center_sq := center_sq2454
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2454.1
  jac_ok := checks2454.2.1
  accepted := checks2454.2.2

def tau2455 : RatBall :=
  ⟨⟨87/320, 87/320⟩, 3/640⟩
def center2455 : GaussianRat :=
  ⟨19714711/100000000, 178023711/1000000000⟩
def contact2455 : RatBall := localContactBall tau2455 center2455
def work2455 : RoundedTauEval :=
  evalTau precision tau2455 contact2455 logTwoBall

theorem center_sq2455 : (center2455.re : ℝ)^2 +
    (center2455.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2455]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2455 : work2455.theta.ok = true ∧
    work2455.jac.invOK = true ∧ acceptsUnitSq work2455.out = true := by
  norm_num [work2455, contact2455, tau2455, center2455, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2455 : CellCertificate where
  tauBall := tau2455
  contactCenter := center2455
  contactBall := contact2455
  work := work2455
  center_sq := center_sq2455
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2455.1
  jac_ok := checks2455.2.1
  accepted := checks2455.2.2

def cells : List CellCertificate := [cell2448, cell2449, cell2450, cell2451, cell2452, cell2453, cell2454, cell2455]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0306
