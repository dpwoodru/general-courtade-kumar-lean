import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0480 : RatBall :=
  ⟨⟨-9/160, -9/32⟩, 3/320⟩
def center0480 : GaussianRat :=
  ⟨-21205027/500000000, -199811247/1000000000⟩
def contact0480 : RatBall := localContactBall tau0480 center0480
def work0480 : RoundedTauEval :=
  evalTau precision tau0480 contact0480 logTwoBall

theorem center_sq0480 : (center0480.re : ℝ)^2 +
    (center0480.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0480]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0480 : work0480.theta.ok = true ∧
    work0480.jac.invOK = true ∧ acceptsUnitSq work0480.out = true := by
  norm_num [work0480, contact0480, tau0480, center0480, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0480 : CellCertificate where
  tauBall := tau0480
  contactCenter := center0480
  contactBall := contact0480
  work := work0480
  center_sq := center_sq0480
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0480.1
  jac_ok := checks0480.2.1
  accepted := checks0480.2.2

def tau0481 : RatBall :=
  ⟨⟨-57/160, -29/160⟩, 3/320⟩
def center0481 : GaussianRat :=
  ⟨-243609941/1000000000, -22312087/200000000⟩
def contact0481 : RatBall := localContactBall tau0481 center0481
def work0481 : RoundedTauEval :=
  evalTau precision tau0481 contact0481 logTwoBall

theorem center_sq0481 : (center0481.re : ℝ)^2 +
    (center0481.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0481]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0481 : work0481.theta.ok = true ∧
    work0481.jac.invOK = true ∧ acceptsUnitSq work0481.out = true := by
  norm_num [work0481, contact0481, tau0481, center0481, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0481 : CellCertificate where
  tauBall := tau0481
  contactCenter := center0481
  contactBall := contact0481
  work := work0481
  center_sq := center_sq0481
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0481.1
  jac_ok := checks0481.2.1
  accepted := checks0481.2.2

def tau0482 : RatBall :=
  ⟨⟨-59/160, -27/160⟩, 3/320⟩
def center0482 : GaussianRat :=
  ⟨-6260393/25000000, -51450627/500000000⟩
def contact0482 : RatBall := localContactBall tau0482 center0482
def work0482 : RoundedTauEval :=
  evalTau precision tau0482 contact0482 logTwoBall

theorem center_sq0482 : (center0482.re : ℝ)^2 +
    (center0482.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0482]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0482 : work0482.theta.ok = true ∧
    work0482.jac.invOK = true ∧ acceptsUnitSq work0482.out = true := by
  norm_num [work0482, contact0482, tau0482, center0482, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0482 : CellCertificate where
  tauBall := tau0482
  contactCenter := center0482
  contactBall := contact0482
  work := work0482
  center_sq := center_sq0482
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0482.1
  jac_ok := checks0482.2.1
  accepted := checks0482.2.2

def tau0483 : RatBall :=
  ⟨⟨-57/160, -27/160⟩, 3/320⟩
def center0483 : GaussianRat :=
  ⟨-242691133/1000000000, -103792249/1000000000⟩
def contact0483 : RatBall := localContactBall tau0483 center0483
def work0483 : RoundedTauEval :=
  evalTau precision tau0483 contact0483 logTwoBall

theorem center_sq0483 : (center0483.re : ℝ)^2 +
    (center0483.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0483]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0483 : work0483.theta.ok = true ∧
    work0483.jac.invOK = true ∧ acceptsUnitSq work0483.out = true := by
  norm_num [work0483, contact0483, tau0483, center0483, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0483 : CellCertificate where
  tauBall := tau0483
  contactCenter := center0483
  contactBall := contact0483
  work := work0483
  center_sq := center_sq0483
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0483.1
  jac_ok := checks0483.2.1
  accepted := checks0483.2.2

def tau0484 : RatBall :=
  ⟨⟨-59/160, -5/32⟩, 3/320⟩
def center0484 : GaussianRat :=
  ⟨-1996423/8000000, -19043899/200000000⟩
def contact0484 : RatBall := localContactBall tau0484 center0484
def work0484 : RoundedTauEval :=
  evalTau precision tau0484 contact0484 logTwoBall

theorem center_sq0484 : (center0484.re : ℝ)^2 +
    (center0484.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0484]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0484 : work0484.theta.ok = true ∧
    work0484.jac.invOK = true ∧ acceptsUnitSq work0484.out = true := by
  norm_num [work0484, contact0484, tau0484, center0484, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0484 : CellCertificate where
  tauBall := tau0484
  contactCenter := center0484
  contactBall := contact0484
  work := work0484
  center_sq := center_sq0484
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0484.1
  jac_ok := checks0484.2.1
  accepted := checks0484.2.2

def tau0485 : RatBall :=
  ⟨⟨-57/160, -5/32⟩, 3/320⟩
def center0485 : GaussianRat :=
  ⟨-7557593/31250000, -96039881/1000000000⟩
def contact0485 : RatBall := localContactBall tau0485 center0485
def work0485 : RoundedTauEval :=
  evalTau precision tau0485 contact0485 logTwoBall

theorem center_sq0485 : (center0485.re : ℝ)^2 +
    (center0485.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0485]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0485 : work0485.theta.ok = true ∧
    work0485.jac.invOK = true ∧ acceptsUnitSq work0485.out = true := by
  norm_num [work0485, contact0485, tau0485, center0485, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0485 : CellCertificate where
  tauBall := tau0485
  contactCenter := center0485
  contactBall := contact0485
  work := work0485
  center_sq := center_sq0485
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0485.1
  jac_ok := checks0485.2.1
  accepted := checks0485.2.2

def tau0486 : RatBall :=
  ⟨⟨-11/32, -31/160⟩, 3/320⟩
def center0486 : GaussianRat :=
  ⟨-47354053/200000000, -30090849/250000000⟩
def contact0486 : RatBall := localContactBall tau0486 center0486
def work0486 : RoundedTauEval :=
  evalTau precision tau0486 contact0486 logTwoBall

theorem center_sq0486 : (center0486.re : ℝ)^2 +
    (center0486.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0486]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0486 : work0486.theta.ok = true ∧
    work0486.jac.invOK = true ∧ acceptsUnitSq work0486.out = true := by
  norm_num [work0486, contact0486, tau0486, center0486, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0486 : CellCertificate where
  tauBall := tau0486
  contactCenter := center0486
  contactBall := contact0486
  work := work0486
  center_sq := center_sq0486
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0486.1
  jac_ok := checks0486.2.1
  accepted := checks0486.2.2

def tau0487 : RatBall :=
  ⟨⟨-53/160, -31/160⟩, 3/320⟩
def center0487 : GaussianRat :=
  ⟨-114433899/500000000, -30340451/250000000⟩
def contact0487 : RatBall := localContactBall tau0487 center0487
def work0487 : RoundedTauEval :=
  evalTau precision tau0487 contact0487 logTwoBall

theorem center_sq0487 : (center0487.re : ℝ)^2 +
    (center0487.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0487]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0487 : work0487.theta.ok = true ∧
    work0487.jac.invOK = true ∧ acceptsUnitSq work0487.out = true := by
  norm_num [work0487, contact0487, tau0487, center0487, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0487 : CellCertificate where
  tauBall := tau0487
  contactCenter := center0487
  contactBall := contact0487
  work := work0487
  center_sq := center_sq0487
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0487.1
  jac_ok := checks0487.2.1
  accepted := checks0487.2.2

def cells : List CellCertificate := [cell0480, cell0481, cell0482, cell0483, cell0484, cell0485, cell0486, cell0487]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060
