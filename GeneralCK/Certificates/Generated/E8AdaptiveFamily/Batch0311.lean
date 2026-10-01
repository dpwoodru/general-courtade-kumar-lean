import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2488 : RatBall :=
  ⟨⟨89/320, 89/320⟩, 3/640⟩
def center2488 : GaussianRat :=
  ⟨40408359/200000000, 181587727/1000000000⟩
def contact2488 : RatBall := localContactBall tau2488 center2488
def work2488 : RoundedTauEval :=
  evalTau precision tau2488 contact2488 logTwoBall

theorem center_sq2488 : (center2488.re : ℝ)^2 +
    (center2488.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2488]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2488 : work2488.theta.ok = true ∧
    work2488.jac.invOK = true ∧ acceptsUnitSq work2488.out = true := by
  norm_num [work2488, contact2488, tau2488, center2488, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2488 : CellCertificate where
  tauBall := tau2488
  contactCenter := center2488
  contactBall := contact2488
  work := work2488
  center_sq := center_sq2488
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2488.1
  jac_ok := checks2488.2.1
  accepted := checks2488.2.2

def tau2489 : RatBall :=
  ⟨⟨91/320, 89/320⟩, 3/640⟩
def center2489 : GaussianRat :=
  ⟨103128439/500000000, 180903081/1000000000⟩
def contact2489 : RatBall := localContactBall tau2489 center2489
def work2489 : RoundedTauEval :=
  evalTau precision tau2489 contact2489 logTwoBall

theorem center_sq2489 : (center2489.re : ℝ)^2 +
    (center2489.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2489]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2489 : work2489.theta.ok = true ∧
    work2489.jac.invOK = true ∧ acceptsUnitSq work2489.out = true := by
  norm_num [work2489, contact2489, tau2489, center2489, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2489 : CellCertificate where
  tauBall := tau2489
  contactCenter := center2489
  contactBall := contact2489
  work := work2489
  center_sq := center_sq2489
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2489.1
  jac_ok := checks2489.2.1
  accepted := checks2489.2.2

def tau2490 : RatBall :=
  ⟨⟨89/320, 91/320⟩, 3/640⟩
def center2490 : GaussianRat :=
  ⟨202731249/1000000000, 37163483/200000000⟩
def contact2490 : RatBall := localContactBall tau2490 center2490
def work2490 : RoundedTauEval :=
  evalTau precision tau2490 contact2490 logTwoBall

theorem center_sq2490 : (center2490.re : ℝ)^2 +
    (center2490.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2490]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2490 : work2490.theta.ok = true ∧
    work2490.jac.invOK = true ∧ acceptsUnitSq work2490.out = true := by
  norm_num [work2490, contact2490, tau2490, center2490, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2490 : CellCertificate where
  tauBall := tau2490
  contactCenter := center2490
  contactBall := contact2490
  work := work2490
  center_sq := center_sq2490
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2490.1
  jac_ok := checks2490.2.1
  accepted := checks2490.2.2

def tau2491 : RatBall :=
  ⟨⟨91/320, 91/320⟩, 3/640⟩
def center2491 : GaussianRat :=
  ⟨51739029/250000000, 46278317/250000000⟩
def contact2491 : RatBall := localContactBall tau2491 center2491
def work2491 : RoundedTauEval :=
  evalTau precision tau2491 contact2491 logTwoBall

theorem center_sq2491 : (center2491.re : ℝ)^2 +
    (center2491.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2491]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2491 : work2491.theta.ok = true ∧
    work2491.jac.invOK = true ∧ acceptsUnitSq work2491.out = true := by
  norm_num [work2491, contact2491, tau2491, center2491, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2491 : CellCertificate where
  tauBall := tau2491
  contactCenter := center2491
  contactBall := contact2491
  work := work2491
  center_sq := center_sq2491
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2491.1
  jac_ok := checks2491.2.1
  accepted := checks2491.2.2

def tau2492 : RatBall :=
  ⟨⟨93/320, 89/320⟩, 3/640⟩
def center2492 : GaussianRat :=
  ⟨84181/400000, 180208911/1000000000⟩
def contact2492 : RatBall := localContactBall tau2492 center2492
def work2492 : RoundedTauEval :=
  evalTau precision tau2492 contact2492 logTwoBall

theorem center_sq2492 : (center2492.re : ℝ)^2 +
    (center2492.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2492]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2492 : work2492.theta.ok = true ∧
    work2492.jac.invOK = true ∧ acceptsUnitSq work2492.out = true := by
  norm_num [work2492, contact2492, tau2492, center2492, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2492 : CellCertificate where
  tauBall := tau2492
  contactCenter := center2492
  contactBall := contact2492
  work := work2492
  center_sq := center_sq2492
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2492.1
  jac_ok := checks2492.2.1
  accepted := checks2492.2.2

def tau2493 : RatBall :=
  ⟨⟨89/320, 93/320⟩, 3/640⟩
def center2493 : GaussianRat :=
  ⟨50860061/250000000, 2969643/15625000⟩
def contact2493 : RatBall := localContactBall tau2493 center2493
def work2493 : RoundedTauEval :=
  evalTau precision tau2493 contact2493 logTwoBall

theorem center_sq2493 : (center2493.re : ℝ)^2 +
    (center2493.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2493]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2493 : work2493.theta.ok = true ∧
    work2493.jac.invOK = true ∧ acceptsUnitSq work2493.out = true := by
  norm_num [work2493, contact2493, tau2493, center2493, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2493 : CellCertificate where
  tauBall := tau2493
  contactCenter := center2493
  contactBall := contact2493
  work := work2493
  center_sq := center_sq2493
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2493.1
  jac_ok := checks2493.2.1
  accepted := checks2493.2.2

def tau2494 : RatBall :=
  ⟨⟨109/320, 13/64⟩, 3/640⟩
def center2494 : GaussianRat :=
  ⟨29446781/125000000, 63266993/500000000⟩
def contact2494 : RatBall := localContactBall tau2494 center2494
def work2494 : RoundedTauEval :=
  evalTau precision tau2494 contact2494 logTwoBall

theorem center_sq2494 : (center2494.re : ℝ)^2 +
    (center2494.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2494]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2494 : work2494.theta.ok = true ∧
    work2494.jac.invOK = true ∧ acceptsUnitSq work2494.out = true := by
  norm_num [work2494, contact2494, tau2494, center2494, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2494 : CellCertificate where
  tauBall := tau2494
  contactCenter := center2494
  contactBall := contact2494
  work := work2494
  center_sq := center_sq2494
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2494.1
  jac_ok := checks2494.2.1
  accepted := checks2494.2.2

def tau2495 : RatBall :=
  ⟨⟨111/320, 13/64⟩, 3/640⟩
def center2495 : GaussianRat :=
  ⟨239515009/1000000000, 31500643/250000000⟩
def contact2495 : RatBall := localContactBall tau2495 center2495
def work2495 : RoundedTauEval :=
  evalTau precision tau2495 contact2495 logTwoBall

theorem center_sq2495 : (center2495.re : ℝ)^2 +
    (center2495.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2495]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2495 : work2495.theta.ok = true ∧
    work2495.jac.invOK = true ∧ acceptsUnitSq work2495.out = true := by
  norm_num [work2495, contact2495, tau2495, center2495, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2495 : CellCertificate where
  tauBall := tau2495
  contactCenter := center2495
  contactBall := contact2495
  work := work2495
  center_sq := center_sq2495
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2495.1
  jac_ok := checks2495.2.1
  accepted := checks2495.2.2

def cells : List CellCertificate := [cell2488, cell2489, cell2490, cell2491, cell2492, cell2493, cell2494, cell2495]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311
