import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0323

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2584 : RatBall :=
  ⟨⟨-23/128, -229/640⟩, 3/1280⟩
def center2584 : GaussianRat :=
  ⟨-70397387/500000000, -249469121/1000000000⟩
def contact2584 : RatBall := localContactBall tau2584 center2584
def work2584 : RoundedTauEval :=
  evalTau precision tau2584 contact2584 logTwoBall

theorem center_sq2584 : (center2584.re : ℝ)^2 +
    (center2584.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2584]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2584 : work2584.theta.ok = true ∧
    work2584.jac.invOK = true ∧ acceptsUnitSq work2584.out = true := by
  norm_num [work2584, contact2584, tau2584, center2584, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2584 : CellCertificate where
  tauBall := tau2584
  contactCenter := center2584
  contactBall := contact2584
  work := work2584
  center_sq := center_sq2584
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2584.1
  jac_ok := checks2584.2.1
  accepted := checks2584.2.2

def tau2585 : RatBall :=
  ⟨⟨-113/640, -229/640⟩, 3/1280⟩
def center2585 : GaussianRat :=
  ⟨-69219087/500000000, -49963011/200000000⟩
def contact2585 : RatBall := localContactBall tau2585 center2585
def work2585 : RoundedTauEval :=
  evalTau precision tau2585 contact2585 logTwoBall

theorem center_sq2585 : (center2585.re : ℝ)^2 +
    (center2585.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2585]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2585 : work2585.theta.ok = true ∧
    work2585.jac.invOK = true ∧ acceptsUnitSq work2585.out = true := by
  norm_num [work2585, contact2585, tau2585, center2585, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2585 : CellCertificate where
  tauBall := tau2585
  contactCenter := center2585
  contactBall := contact2585
  work := work2585
  center_sq := center_sq2585
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2585.1
  jac_ok := checks2585.2.1
  accepted := checks2585.2.2

def tau2586 : RatBall :=
  ⟨⟨-119/640, -227/640⟩, 3/1280⟩
def center2586 : GaussianRat :=
  ⟨-145138173/1000000000, -123210011/500000000⟩
def contact2586 : RatBall := localContactBall tau2586 center2586
def work2586 : RoundedTauEval :=
  evalTau precision tau2586 contact2586 logTwoBall

theorem center_sq2586 : (center2586.re : ℝ)^2 +
    (center2586.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2586]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2586 : work2586.theta.ok = true ∧
    work2586.jac.invOK = true ∧ acceptsUnitSq work2586.out = true := by
  norm_num [work2586, contact2586, tau2586, center2586, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2586 : CellCertificate where
  tauBall := tau2586
  contactCenter := center2586
  contactBall := contact2586
  work := work2586
  center_sq := center_sq2586
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2586.1
  jac_ok := checks2586.2.1
  accepted := checks2586.2.2

def tau2587 : RatBall :=
  ⟨⟨-117/640, -227/640⟩, 3/1280⟩
def center2587 : GaussianRat :=
  ⟨-142795751/1000000000, -246771071/1000000000⟩
def contact2587 : RatBall := localContactBall tau2587 center2587
def work2587 : RoundedTauEval :=
  evalTau precision tau2587 contact2587 logTwoBall

theorem center_sq2587 : (center2587.re : ℝ)^2 +
    (center2587.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2587]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2587 : work2587.theta.ok = true ∧
    work2587.jac.invOK = true ∧ acceptsUnitSq work2587.out = true := by
  norm_num [work2587, contact2587, tau2587, center2587, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2587 : CellCertificate where
  tauBall := tau2587
  contactCenter := center2587
  contactBall := contact2587
  work := work2587
  center_sq := center_sq2587
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2587.1
  jac_ok := checks2587.2.1
  accepted := checks2587.2.2

def tau2588 : RatBall :=
  ⟨⟨-119/640, -45/128⟩, 3/1280⟩
def center2588 : GaussianRat :=
  ⟨-72393537/500000000, -122041161/500000000⟩
def contact2588 : RatBall := localContactBall tau2588 center2588
def work2588 : RoundedTauEval :=
  evalTau precision tau2588 contact2588 logTwoBall

theorem center_sq2588 : (center2588.re : ℝ)^2 +
    (center2588.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2588]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2588 : work2588.theta.ok = true ∧
    work2588.jac.invOK = true ∧ acceptsUnitSq work2588.out = true := by
  norm_num [work2588, contact2588, tau2588, center2588, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2588 : CellCertificate where
  tauBall := tau2588
  contactCenter := center2588
  contactBall := contact2588
  work := work2588
  center_sq := center_sq2588
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2588.1
  jac_ok := checks2588.2.1
  accepted := checks2588.2.2

def tau2589 : RatBall :=
  ⟨⟨-117/640, -45/128⟩, 3/1280⟩
def center2589 : GaussianRat :=
  ⟨-8903089/62500000, -244428717/1000000000⟩
def contact2589 : RatBall := localContactBall tau2589 center2589
def work2589 : RoundedTauEval :=
  evalTau precision tau2589 contact2589 logTwoBall

theorem center_sq2589 : (center2589.re : ℝ)^2 +
    (center2589.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2589]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2589 : work2589.theta.ok = true ∧
    work2589.jac.invOK = true ∧ acceptsUnitSq work2589.out = true := by
  norm_num [work2589, contact2589, tau2589, center2589, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2589 : CellCertificate where
  tauBall := tau2589
  contactCenter := center2589
  contactBall := contact2589
  work := work2589
  center_sq := center_sq2589
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2589.1
  jac_ok := checks2589.2.1
  accepted := checks2589.2.2

def tau2590 : RatBall :=
  ⟨⟨-23/128, -227/640⟩, 3/1280⟩
def center2590 : GaussianRat :=
  ⟨-140448677/1000000000, -247117293/1000000000⟩
def contact2590 : RatBall := localContactBall tau2590 center2590
def work2590 : RoundedTauEval :=
  evalTau precision tau2590 contact2590 logTwoBall

theorem center_sq2590 : (center2590.re : ℝ)^2 +
    (center2590.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2590]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2590 : work2590.theta.ok = true ∧
    work2590.jac.invOK = true ∧ acceptsUnitSq work2590.out = true := by
  norm_num [work2590, contact2590, tau2590, center2590, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2590 : CellCertificate where
  tauBall := tau2590
  contactCenter := center2590
  contactBall := contact2590
  work := work2590
  center_sq := center_sq2590
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2590.1
  jac_ok := checks2590.2.1
  accepted := checks2590.2.2

def tau2591 : RatBall :=
  ⟨⟨-113/640, -227/640⟩, 3/1280⟩
def center2591 : GaussianRat :=
  ⟨-138097011/1000000000, -61864659/250000000⟩
def contact2591 : RatBall := localContactBall tau2591 center2591
def work2591 : RoundedTauEval :=
  evalTau precision tau2591 contact2591 logTwoBall

theorem center_sq2591 : (center2591.re : ℝ)^2 +
    (center2591.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2591]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2591 : work2591.theta.ok = true ∧
    work2591.jac.invOK = true ∧ acceptsUnitSq work2591.out = true := by
  norm_num [work2591, contact2591, tau2591, center2591, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2591 : CellCertificate where
  tauBall := tau2591
  contactCenter := center2591
  contactBall := contact2591
  work := work2591
  center_sq := center_sq2591
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2591.1
  jac_ok := checks2591.2.1
  accepted := checks2591.2.2

def cells : List CellCertificate := [cell2584, cell2585, cell2586, cell2587, cell2588, cell2589, cell2590, cell2591]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0323
