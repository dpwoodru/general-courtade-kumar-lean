import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0696 : RatBall :=
  ⟨⟨39/160, -31/160⟩, 3/320⟩
def center0696 : GaussianRat :=
  ⟨10728219/62500000, -127685733/1000000000⟩
def contact0696 : RatBall := localContactBall tau0696 center0696
def work0696 : RoundedTauEval :=
  evalTau precision tau0696 contact0696 logTwoBall

theorem center_sq0696 : (center0696.re : ℝ)^2 +
    (center0696.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0696]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0696 : work0696.theta.ok = true ∧
    work0696.jac.invOK = true ∧ acceptsUnitSq work0696.out = true := by
  norm_num [work0696, contact0696, tau0696, center0696, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0696 : CellCertificate where
  tauBall := tau0696
  contactCenter := center0696
  contactBall := contact0696
  work := work0696
  center_sq := center_sq0696
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0696.1
  jac_ok := checks0696.2.1
  accepted := checks0696.2.2

def tau0697 : RatBall :=
  ⟨⟨37/160, -29/160⟩, 3/320⟩
def center0697 : GaussianRat :=
  ⟨81239917/500000000, -60019727/500000000⟩
def contact0697 : RatBall := localContactBall tau0697 center0697
def work0697 : RoundedTauEval :=
  evalTau precision tau0697 contact0697 logTwoBall

theorem center_sq0697 : (center0697.re : ℝ)^2 +
    (center0697.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0697]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0697 : work0697.theta.ok = true ∧
    work0697.jac.invOK = true ∧ acceptsUnitSq work0697.out = true := by
  norm_num [work0697, contact0697, tau0697, center0697, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0697 : CellCertificate where
  tauBall := tau0697
  contactCenter := center0697
  contactBall := contact0697
  work := work0697
  center_sq := center_sq0697
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0697.1
  jac_ok := checks0697.2.1
  accepted := checks0697.2.2

def tau0698 : RatBall :=
  ⟨⟨39/160, -29/160⟩, 3/320⟩
def center0698 : GaussianRat :=
  ⟨2135923/12500000, -119305389/1000000000⟩
def contact0698 : RatBall := localContactBall tau0698 center0698
def work0698 : RoundedTauEval :=
  evalTau precision tau0698 contact0698 logTwoBall

theorem center_sq0698 : (center0698.re : ℝ)^2 +
    (center0698.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0698]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0698 : work0698.theta.ok = true ∧
    work0698.jac.invOK = true ∧ acceptsUnitSq work0698.out = true := by
  norm_num [work0698, contact0698, tau0698, center0698, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0698 : CellCertificate where
  tauBall := tau0698
  contactCenter := center0698
  contactBall := contact0698
  work := work0698
  center_sq := center_sq0698
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0698.1
  jac_ok := checks0698.2.1
  accepted := checks0698.2.2

def tau0699 : RatBall :=
  ⟨⟨41/160, -31/160⟩, 3/320⟩
def center0699 : GaussianRat :=
  ⟨36003433/200000000, -3171591/25000000⟩
def contact0699 : RatBall := localContactBall tau0699 center0699
def work0699 : RoundedTauEval :=
  evalTau precision tau0699 contact0699 logTwoBall

theorem center_sq0699 : (center0699.re : ℝ)^2 +
    (center0699.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0699]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0699 : work0699.theta.ok = true ∧
    work0699.jac.invOK = true ∧ acceptsUnitSq work0699.out = true := by
  norm_num [work0699, contact0699, tau0699, center0699, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0699 : CellCertificate where
  tauBall := tau0699
  contactCenter := center0699
  contactBall := contact0699
  work := work0699
  center_sq := center_sq0699
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0699.1
  jac_ok := checks0699.2.1
  accepted := checks0699.2.2

def tau0700 : RatBall :=
  ⟨⟨43/160, -31/160⟩, 3/320⟩
def center0700 : GaussianRat :=
  ⟨188321901/1000000000, -126012049/1000000000⟩
def contact0700 : RatBall := localContactBall tau0700 center0700
def work0700 : RoundedTauEval :=
  evalTau precision tau0700 contact0700 logTwoBall

theorem center_sq0700 : (center0700.re : ℝ)^2 +
    (center0700.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0700]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0700 : work0700.theta.ok = true ∧
    work0700.jac.invOK = true ∧ acceptsUnitSq work0700.out = true := by
  norm_num [work0700, contact0700, tau0700, center0700, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0700 : CellCertificate where
  tauBall := tau0700
  contactCenter := center0700
  contactBall := contact0700
  work := work0700
  center_sq := center_sq0700
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0700.1
  jac_ok := checks0700.2.1
  accepted := checks0700.2.2

def tau0701 : RatBall :=
  ⟨⟨41/160, -29/160⟩, 3/320⟩
def center0701 : GaussianRat :=
  ⟨89605161/500000000, -4741701/40000000⟩
def contact0701 : RatBall := localContactBall tau0701 center0701
def work0701 : RoundedTauEval :=
  evalTau precision tau0701 contact0701 logTwoBall

theorem center_sq0701 : (center0701.re : ℝ)^2 +
    (center0701.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0701]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0701 : work0701.theta.ok = true ∧
    work0701.jac.invOK = true ∧ acceptsUnitSq work0701.out = true := by
  norm_num [work0701, contact0701, tau0701, center0701, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0701 : CellCertificate where
  tauBall := tau0701
  contactCenter := center0701
  contactBall := contact0701
  work := work0701
  center_sq := center_sq0701
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0701.1
  jac_ok := checks0701.2.1
  accepted := checks0701.2.2

def tau0702 : RatBall :=
  ⟨⟨43/160, -29/160⟩, 3/320⟩
def center0702 : GaussianRat :=
  ⟨187487239/1000000000, -23550431/200000000⟩
def contact0702 : RatBall := localContactBall tau0702 center0702
def work0702 : RoundedTauEval :=
  evalTau precision tau0702 contact0702 logTwoBall

theorem center_sq0702 : (center0702.re : ℝ)^2 +
    (center0702.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0702]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0702 : work0702.theta.ok = true ∧
    work0702.jac.invOK = true ∧ acceptsUnitSq work0702.out = true := by
  norm_num [work0702, contact0702, tau0702, center0702, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0702 : CellCertificate where
  tauBall := tau0702
  contactCenter := center0702
  contactBall := contact0702
  work := work0702
  center_sq := center_sq0702
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0702.1
  jac_ok := checks0702.2.1
  accepted := checks0702.2.2

def tau0703 : RatBall :=
  ⟨⟨9/32, -31/160⟩, 3/320⟩
def center0703 : GaussianRat :=
  ⟨19656377/100000000, -125132383/1000000000⟩
def contact0703 : RatBall := localContactBall tau0703 center0703
def work0703 : RoundedTauEval :=
  evalTau precision tau0703 contact0703 logTwoBall

theorem center_sq0703 : (center0703.re : ℝ)^2 +
    (center0703.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0703]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0703 : work0703.theta.ok = true ∧
    work0703.jac.invOK = true ∧ acceptsUnitSq work0703.out = true := by
  norm_num [work0703, contact0703, tau0703, center0703, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0703 : CellCertificate where
  tauBall := tau0703
  contactCenter := center0703
  contactBall := contact0703
  work := work0703
  center_sq := center_sq0703
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0703.1
  jac_ok := checks0703.2.1
  accepted := checks0703.2.2

def cells : List CellCertificate := [cell0696, cell0697, cell0698, cell0699, cell0700, cell0701, cell0702, cell0703]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087
