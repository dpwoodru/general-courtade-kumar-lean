import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0368 : RatBall :=
  ⟨⟨-41/160, -37/160⟩, 3/320⟩
def center0368 : GaussianRat :=
  ⟨-182809387/1000000000, -76006029/500000000⟩
def contact0368 : RatBall := localContactBall tau0368 center0368
def work0368 : RoundedTauEval :=
  evalTau precision tau0368 contact0368 logTwoBall

theorem center_sq0368 : (center0368.re : ℝ)^2 +
    (center0368.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0368]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0368 : work0368.theta.ok = true ∧
    work0368.jac.invOK = true ∧ acceptsUnitSq work0368.out = true := by
  norm_num [work0368, contact0368, tau0368, center0368, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0368 : CellCertificate where
  tauBall := tau0368
  contactCenter := center0368
  contactBall := contact0368
  work := work0368
  center_sq := center_sq0368
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0368.1
  jac_ok := checks0368.2.1
  accepted := checks0368.2.2

def tau0369 : RatBall :=
  ⟨⟨-47/160, -7/32⟩, 3/320⟩
def center0369 : GaussianRat :=
  ⟨-206714057/1000000000, -70283583/500000000⟩
def contact0369 : RatBall := localContactBall tau0369 center0369
def work0369 : RoundedTauEval :=
  evalTau precision tau0369 contact0369 logTwoBall

theorem center_sq0369 : (center0369.re : ℝ)^2 +
    (center0369.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0369]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0369 : work0369.theta.ok = true ∧
    work0369.jac.invOK = true ∧ acceptsUnitSq work0369.out = true := by
  norm_num [work0369, contact0369, tau0369, center0369, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0369 : CellCertificate where
  tauBall := tau0369
  contactCenter := center0369
  contactBall := contact0369
  work := work0369
  center_sq := center_sq0369
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0369.1
  jac_ok := checks0369.2.1
  accepted := checks0369.2.2

def tau0370 : RatBall :=
  ⟨⟨-9/32, -7/32⟩, 3/320⟩
def center0370 : GaussianRat :=
  ⟨-49620407/250000000, -141607653/1000000000⟩
def contact0370 : RatBall := localContactBall tau0370 center0370
def work0370 : RoundedTauEval :=
  evalTau precision tau0370 contact0370 logTwoBall

theorem center_sq0370 : (center0370.re : ℝ)^2 +
    (center0370.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0370]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0370 : work0370.theta.ok = true ∧
    work0370.jac.invOK = true ∧ acceptsUnitSq work0370.out = true := by
  norm_num [work0370, contact0370, tau0370, center0370, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0370 : CellCertificate where
  tauBall := tau0370
  contactCenter := center0370
  contactBall := contact0370
  work := work0370
  center_sq := center_sq0370
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0370.1
  jac_ok := checks0370.2.1
  accepted := checks0370.2.2

def tau0371 : RatBall :=
  ⟨⟨-47/160, -33/160⟩, 3/320⟩
def center0371 : GaussianRat :=
  ⟨-205693537/1000000000, -132383201/1000000000⟩
def contact0371 : RatBall := localContactBall tau0371 center0371
def work0371 : RoundedTauEval :=
  evalTau precision tau0371 contact0371 logTwoBall

theorem center_sq0371 : (center0371.re : ℝ)^2 +
    (center0371.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0371]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0371 : work0371.theta.ok = true ∧
    work0371.jac.invOK = true ∧ acceptsUnitSq work0371.out = true := by
  norm_num [work0371, contact0371, tau0371, center0371, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0371 : CellCertificate where
  tauBall := tau0371
  contactCenter := center0371
  contactBall := contact0371
  work := work0371
  center_sq := center_sq0371
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0371.1
  jac_ok := checks0371.2.1
  accepted := checks0371.2.2

def tau0372 : RatBall :=
  ⟨⟨-9/32, -33/160⟩, 3/320⟩
def center0372 : GaussianRat :=
  ⟨-197489591/1000000000, -66677907/500000000⟩
def contact0372 : RatBall := localContactBall tau0372 center0372
def work0372 : RoundedTauEval :=
  evalTau precision tau0372 contact0372 logTwoBall

theorem center_sq0372 : (center0372.re : ℝ)^2 +
    (center0372.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0372]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0372 : work0372.theta.ok = true ∧
    work0372.jac.invOK = true ∧ acceptsUnitSq work0372.out = true := by
  norm_num [work0372, contact0372, tau0372, center0372, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0372 : CellCertificate where
  tauBall := tau0372
  contactCenter := center0372
  contactBall := contact0372
  work := work0372
  center_sq := center_sq0372
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0372.1
  jac_ok := checks0372.2.1
  accepted := checks0372.2.2

def tau0373 : RatBall :=
  ⟨⟨-43/160, -7/32⟩, 3/320⟩
def center0373 : GaussianRat :=
  ⟨-9509069/50000000, -71308977/500000000⟩
def contact0373 : RatBall := localContactBall tau0373 center0373
def work0373 : RoundedTauEval :=
  evalTau precision tau0373 contact0373 logTwoBall

theorem center_sq0373 : (center0373.re : ℝ)^2 +
    (center0373.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0373]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0373 : work0373.theta.ok = true ∧
    work0373.jac.invOK = true ∧ acceptsUnitSq work0373.out = true := by
  norm_num [work0373, contact0373, tau0373, center0373, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0373 : CellCertificate where
  tauBall := tau0373
  contactCenter := center0373
  contactBall := contact0373
  work := work0373
  center_sq := center_sq0373
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0373.1
  jac_ok := checks0373.2.1
  accepted := checks0373.2.2

def tau0374 : RatBall :=
  ⟨⟨-41/160, -7/32⟩, 3/320⟩
def center0374 : GaussianRat :=
  ⟨-90907579/500000000, -143596387/1000000000⟩
def contact0374 : RatBall := localContactBall tau0374 center0374
def work0374 : RoundedTauEval :=
  evalTau precision tau0374 contact0374 logTwoBall

theorem center_sq0374 : (center0374.re : ℝ)^2 +
    (center0374.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0374]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0374 : work0374.theta.ok = true ∧
    work0374.jac.invOK = true ∧ acceptsUnitSq work0374.out = true := by
  norm_num [work0374, contact0374, tau0374, center0374, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0374 : CellCertificate where
  tauBall := tau0374
  contactCenter := center0374
  contactBall := contact0374
  work := work0374
  center_sq := center_sq0374
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0374.1
  jac_ok := checks0374.2.1
  accepted := checks0374.2.2

def tau0375 : RatBall :=
  ⟨⟨-43/160, -33/160⟩, 3/320⟩
def center0375 : GaussianRat :=
  ⟨-189219451/1000000000, -67150009/500000000⟩
def contact0375 : RatBall := localContactBall tau0375 center0375
def work0375 : RoundedTauEval :=
  evalTau precision tau0375 contact0375 logTwoBall

theorem center_sq0375 : (center0375.re : ℝ)^2 +
    (center0375.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0375]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0375 : work0375.theta.ok = true ∧
    work0375.jac.invOK = true ∧ acceptsUnitSq work0375.out = true := by
  norm_num [work0375, contact0375, tau0375, center0375, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0375 : CellCertificate where
  tauBall := tau0375
  contactCenter := center0375
  contactBall := contact0375
  work := work0375
  center_sq := center_sq0375
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0375.1
  jac_ok := checks0375.2.1
  accepted := checks0375.2.2

def cells : List CellCertificate := [cell0368, cell0369, cell0370, cell0371, cell0372, cell0373, cell0374, cell0375]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046
