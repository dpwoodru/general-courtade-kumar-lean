import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0316

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2528 : RatBall :=
  ⟨⟨13/64, 101/320⟩, 3/640⟩
def center2528 : GaussianRat :=
  ⟨38393397/250000000, 26977781/125000000⟩
def contact2528 : RatBall := localContactBall tau2528 center2528
def work2528 : RoundedTauEval :=
  evalTau precision tau2528 contact2528 logTwoBall

theorem center_sq2528 : (center2528.re : ℝ)^2 +
    (center2528.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2528]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2528 : work2528.theta.ok = true ∧
    work2528.jac.invOK = true ∧ acceptsUnitSq work2528.out = true := by
  norm_num [work2528, contact2528, tau2528, center2528, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2528 : CellCertificate where
  tauBall := tau2528
  contactCenter := center2528
  contactBall := contact2528
  work := work2528
  center_sq := center_sq2528
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2528.1
  jac_ok := checks2528.2.1
  accepted := checks2528.2.2

def tau2529 : RatBall :=
  ⟨⟨67/320, 101/320⟩, 3/640⟩
def center2529 : GaussianRat :=
  ⟨158087121/1000000000, 215173931/1000000000⟩
def contact2529 : RatBall := localContactBall tau2529 center2529
def work2529 : RoundedTauEval :=
  evalTau precision tau2529 contact2529 logTwoBall

theorem center_sq2529 : (center2529.re : ℝ)^2 +
    (center2529.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2529]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2529 : work2529.theta.ok = true ∧
    work2529.jac.invOK = true ∧ acceptsUnitSq work2529.out = true := by
  norm_num [work2529, contact2529, tau2529, center2529, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2529 : CellCertificate where
  tauBall := tau2529
  contactCenter := center2529
  contactBall := contact2529
  work := work2529
  center_sq := center_sq2529
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2529.1
  jac_ok := checks2529.2.1
  accepted := checks2529.2.2

def tau2530 : RatBall :=
  ⟨⟨13/64, 103/320⟩, 3/640⟩
def center2530 : GaussianRat :=
  ⟨154223071/1000000000, 110176223/500000000⟩
def contact2530 : RatBall := localContactBall tau2530 center2530
def work2530 : RoundedTauEval :=
  evalTau precision tau2530 contact2530 logTwoBall

theorem center_sq2530 : (center2530.re : ℝ)^2 +
    (center2530.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2530]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2530 : work2530.theta.ok = true ∧
    work2530.jac.invOK = true ∧ acceptsUnitSq work2530.out = true := by
  norm_num [work2530, contact2530, tau2530, center2530, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2530 : CellCertificate where
  tauBall := tau2530
  contactCenter := center2530
  contactBall := contact2530
  work := work2530
  center_sq := center_sq2530
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2530.1
  jac_ok := checks2530.2.1
  accepted := checks2530.2.2

def tau2531 : RatBall :=
  ⟨⟨67/320, 103/320⟩, 3/640⟩
def center2531 : GaussianRat :=
  ⟨79376053/500000000, 109843089/500000000⟩
def contact2531 : RatBall := localContactBall tau2531 center2531
def work2531 : RoundedTauEval :=
  evalTau precision tau2531 contact2531 logTwoBall

theorem center_sq2531 : (center2531.re : ℝ)^2 +
    (center2531.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2531]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2531 : work2531.theta.ok = true ∧
    work2531.jac.invOK = true ∧ acceptsUnitSq work2531.out = true := by
  norm_num [work2531, contact2531, tau2531, center2531, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2531 : CellCertificate where
  tauBall := tau2531
  contactCenter := center2531
  contactBall := contact2531
  work := work2531
  center_sq := center_sq2531
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2531.1
  jac_ok := checks2531.2.1
  accepted := checks2531.2.2

def tau2532 : RatBall :=
  ⟨⟨69/320, 101/320⟩, 3/640⟩
def center2532 : GaussianRat :=
  ⟨32516539/200000000, 26813809/125000000⟩
def contact2532 : RatBall := localContactBall tau2532 center2532
def work2532 : RoundedTauEval :=
  evalTau precision tau2532 contact2532 logTwoBall

theorem center_sq2532 : (center2532.re : ℝ)^2 +
    (center2532.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2532]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2532 : work2532.theta.ok = true ∧
    work2532.jac.invOK = true ∧ acceptsUnitSq work2532.out = true := by
  norm_num [work2532, contact2532, tau2532, center2532, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2532 : CellCertificate where
  tauBall := tau2532
  contactCenter := center2532
  contactBall := contact2532
  work := work2532
  center_sq := center_sq2532
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2532.1
  jac_ok := checks2532.2.1
  accepted := checks2532.2.2

def tau2533 : RatBall :=
  ⟨⟨71/320, 101/320⟩, 3/640⟩
def center2533 : GaussianRat :=
  ⟨167059951/1000000000, 10691611/50000000⟩
def contact2533 : RatBall := localContactBall tau2533 center2533
def work2533 : RoundedTauEval :=
  evalTau precision tau2533 contact2533 logTwoBall

theorem center_sq2533 : (center2533.re : ℝ)^2 +
    (center2533.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2533]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2533 : work2533.theta.ok = true ∧
    work2533.jac.invOK = true ∧ acceptsUnitSq work2533.out = true := by
  norm_num [work2533, contact2533, tau2533, center2533, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2533 : CellCertificate where
  tauBall := tau2533
  contactCenter := center2533
  contactBall := contact2533
  work := work2533
  center_sq := center_sq2533
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2533.1
  jac_ok := checks2533.2.1
  accepted := checks2533.2.2

def tau2534 : RatBall :=
  ⟨⟨69/320, 103/320⟩, 3/640⟩
def center2534 : GaussianRat :=
  ⟨40815707/250000000, 219004401/1000000000⟩
def contact2534 : RatBall := localContactBall tau2534 center2534
def work2534 : RoundedTauEval :=
  evalTau precision tau2534 contact2534 logTwoBall

theorem center_sq2534 : (center2534.re : ℝ)^2 +
    (center2534.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2534]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2534 : work2534.theta.ok = true ∧
    work2534.jac.invOK = true ∧ acceptsUnitSq work2534.out = true := by
  norm_num [work2534, contact2534, tau2534, center2534, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2534 : CellCertificate where
  tauBall := tau2534
  contactCenter := center2534
  contactBall := contact2534
  work := work2534
  center_sq := center_sq2534
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2534.1
  jac_ok := checks2534.2.1
  accepted := checks2534.2.2

def tau2535 : RatBall :=
  ⟨⟨71/320, 103/320⟩, 3/640⟩
def center2535 : GaussianRat :=
  ⟨83877437/500000000, 218307477/1000000000⟩
def contact2535 : RatBall := localContactBall tau2535 center2535
def work2535 : RoundedTauEval :=
  evalTau precision tau2535 contact2535 logTwoBall

theorem center_sq2535 : (center2535.re : ℝ)^2 +
    (center2535.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2535]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2535 : work2535.theta.ok = true ∧
    work2535.jac.invOK = true ∧ acceptsUnitSq work2535.out = true := by
  norm_num [work2535, contact2535, tau2535, center2535, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2535 : CellCertificate where
  tauBall := tau2535
  contactCenter := center2535
  contactBall := contact2535
  work := work2535
  center_sq := center_sq2535
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2535.1
  jac_ok := checks2535.2.1
  accepted := checks2535.2.2

def cells : List CellCertificate := [cell2528, cell2529, cell2530, cell2531, cell2532, cell2533, cell2534, cell2535]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0316
