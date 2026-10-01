import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0456 : RatBall :=
  ⟨⟨-17/160, -9/32⟩, 3/320⟩
def center0456 : GaussianRat :=
  ⟨-19945259/250000000, -39579621/200000000⟩
def contact0456 : RatBall := localContactBall tau0456 center0456
def work0456 : RoundedTauEval :=
  evalTau precision tau0456 contact0456 logTwoBall

theorem center_sq0456 : (center0456.re : ℝ)^2 +
    (center0456.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0456]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0456 : work0456.theta.ok = true ∧
    work0456.jac.invOK = true ∧ acceptsUnitSq work0456.out = true := by
  norm_num [work0456, contact0456, tau0456, center0456, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0456 : CellCertificate where
  tauBall := tau0456
  contactCenter := center0456
  contactBall := contact0456
  work := work0456
  center_sq := center_sq0456
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0456.1
  jac_ok := checks0456.2.1
  accepted := checks0456.2.2

def tau0457 : RatBall :=
  ⟨⟨-23/160, -43/160⟩, 3/320⟩
def center0457 : GaussianRat :=
  ⟨-106644393/1000000000, -93309307/500000000⟩
def contact0457 : RatBall := localContactBall tau0457 center0457
def work0457 : RoundedTauEval :=
  evalTau precision tau0457 contact0457 logTwoBall

theorem center_sq0457 : (center0457.re : ℝ)^2 +
    (center0457.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0457]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0457 : work0457.theta.ok = true ∧
    work0457.jac.invOK = true ∧ acceptsUnitSq work0457.out = true := by
  norm_num [work0457, contact0457, tau0457, center0457, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0457 : CellCertificate where
  tauBall := tau0457
  contactCenter := center0457
  contactBall := contact0457
  work := work0457
  center_sq := center_sq0457
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0457.1
  jac_ok := checks0457.2.1
  accepted := checks0457.2.2

def tau0458 : RatBall :=
  ⟨⟨-21/160, -43/160⟩, 3/320⟩
def center0458 : GaussianRat :=
  ⟨-1523927/15625000, -46839637/250000000⟩
def contact0458 : RatBall := localContactBall tau0458 center0458
def work0458 : RoundedTauEval :=
  evalTau precision tau0458 contact0458 logTwoBall

theorem center_sq0458 : (center0458.re : ℝ)^2 +
    (center0458.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0458]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0458 : work0458.theta.ok = true ∧
    work0458.jac.invOK = true ∧ acceptsUnitSq work0458.out = true := by
  norm_num [work0458, contact0458, tau0458, center0458, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0458 : CellCertificate where
  tauBall := tau0458
  contactCenter := center0458
  contactBall := contact0458
  work := work0458
  center_sq := center_sq0458
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0458.1
  jac_ok := checks0458.2.1
  accepted := checks0458.2.2

def tau0459 : RatBall :=
  ⟨⟨-23/160, -41/160⟩, 3/320⟩
def center0459 : GaussianRat :=
  ⟨-105897059/1000000000, -22194707/125000000⟩
def contact0459 : RatBall := localContactBall tau0459 center0459
def work0459 : RoundedTauEval :=
  evalTau precision tau0459 contact0459 logTwoBall

theorem center_sq0459 : (center0459.re : ℝ)^2 +
    (center0459.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0459]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0459 : work0459.theta.ok = true ∧
    work0459.jac.invOK = true ∧ acceptsUnitSq work0459.out = true := by
  norm_num [work0459, contact0459, tau0459, center0459, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0459 : CellCertificate where
  tauBall := tau0459
  contactCenter := center0459
  contactBall := contact0459
  work := work0459
  center_sq := center_sq0459
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0459.1
  jac_ok := checks0459.2.1
  accepted := checks0459.2.2

def tau0460 : RatBall :=
  ⟨⟨-21/160, -41/160⟩, 3/320⟩
def center0460 : GaussianRat :=
  ⟨-96843181/1000000000, -5570429/31250000⟩
def contact0460 : RatBall := localContactBall tau0460 center0460
def work0460 : RoundedTauEval :=
  evalTau precision tau0460 contact0460 logTwoBall

theorem center_sq0460 : (center0460.re : ℝ)^2 +
    (center0460.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0460 : work0460.theta.ok = true ∧
    work0460.jac.invOK = true ∧ acceptsUnitSq work0460.out = true := by
  norm_num [work0460, contact0460, tau0460, center0460, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0460 : CellCertificate where
  tauBall := tau0460
  contactCenter := center0460
  contactBall := contact0460
  work := work0460
  center_sq := center_sq0460
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0460.1
  jac_ok := checks0460.2.1
  accepted := checks0460.2.2

def tau0461 : RatBall :=
  ⟨⟨-19/160, -43/160⟩, 3/320⟩
def center0461 : GaussianRat :=
  ⟨-88375401/1000000000, -188036739/1000000000⟩
def contact0461 : RatBall := localContactBall tau0461 center0461
def work0461 : RoundedTauEval :=
  evalTau precision tau0461 contact0461 logTwoBall

theorem center_sq0461 : (center0461.re : ℝ)^2 +
    (center0461.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0461]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0461 : work0461.theta.ok = true ∧
    work0461.jac.invOK = true ∧ acceptsUnitSq work0461.out = true := by
  norm_num [work0461, contact0461, tau0461, center0461, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0461 : CellCertificate where
  tauBall := tau0461
  contactCenter := center0461
  contactBall := contact0461
  work := work0461
  center_sq := center_sq0461
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0461.1
  jac_ok := checks0461.2.1
  accepted := checks0461.2.2

def tau0462 : RatBall :=
  ⟨⟨-17/160, -43/160⟩, 3/320⟩
def center0462 : GaussianRat :=
  ⟨-39590143/500000000, -47162917/250000000⟩
def contact0462 : RatBall := localContactBall tau0462 center0462
def work0462 : RoundedTauEval :=
  evalTau precision tau0462 contact0462 logTwoBall

theorem center_sq0462 : (center0462.re : ℝ)^2 +
    (center0462.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0462]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0462 : work0462.theta.ok = true ∧
    work0462.jac.invOK = true ∧ acceptsUnitSq work0462.out = true := by
  norm_num [work0462, contact0462, tau0462, center0462, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0462 : CellCertificate where
  tauBall := tau0462
  contactCenter := center0462
  contactBall := contact0462
  work := work0462
  center_sq := center_sq0462
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0462.1
  jac_ok := checks0462.2.1
  accepted := checks0462.2.2

def tau0463 : RatBall :=
  ⟨⟨-19/160, -41/160⟩, 3/320⟩
def center0463 : GaussianRat :=
  ⟨-43873979/500000000, -35778323/200000000⟩
def contact0463 : RatBall := localContactBall tau0463 center0463
def work0463 : RoundedTauEval :=
  evalTau precision tau0463 contact0463 logTwoBall

theorem center_sq0463 : (center0463.re : ℝ)^2 +
    (center0463.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0463]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0463 : work0463.theta.ok = true ∧
    work0463.jac.invOK = true ∧ acceptsUnitSq work0463.out = true := by
  norm_num [work0463, contact0463, tau0463, center0463, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0463 : CellCertificate where
  tauBall := tau0463
  contactCenter := center0463
  contactBall := contact0463
  work := work0463
  center_sq := center_sq0463
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0463.1
  jac_ok := checks0463.2.1
  accepted := checks0463.2.2

def cells : List CellCertificate := [cell0456, cell0457, cell0458, cell0459, cell0460, cell0461, cell0462, cell0463]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057
