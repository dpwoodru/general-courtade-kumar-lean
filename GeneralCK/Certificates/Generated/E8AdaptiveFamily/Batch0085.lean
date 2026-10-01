import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0680 : RatBall :=
  ⟨⟨47/160, -37/160⟩, 3/320⟩
def center0680 : GaussianRat :=
  ⟨103902067/500000000, -37194907/250000000⟩
def contact0680 : RatBall := localContactBall tau0680 center0680
def work0680 : RoundedTauEval :=
  evalTau precision tau0680 contact0680 logTwoBall

theorem center_sq0680 : (center0680.re : ℝ)^2 +
    (center0680.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0680]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0680 : work0680.theta.ok = true ∧
    work0680.jac.invOK = true ∧ acceptsUnitSq work0680.out = true := by
  norm_num [work0680, contact0680, tau0680, center0680, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0680 : CellCertificate where
  tauBall := tau0680
  contactCenter := center0680
  contactBall := contact0680
  work := work0680
  center_sq := center_sq0680
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0680.1
  jac_ok := checks0680.2.1
  accepted := checks0680.2.2

def tau0681 : RatBall :=
  ⟨⟨41/160, -7/32⟩, 3/320⟩
def center0681 : GaussianRat :=
  ⟨90907579/500000000, -143596387/1000000000⟩
def contact0681 : RatBall := localContactBall tau0681 center0681
def work0681 : RoundedTauEval :=
  evalTau precision tau0681 contact0681 logTwoBall

theorem center_sq0681 : (center0681.re : ℝ)^2 +
    (center0681.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0681]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0681 : work0681.theta.ok = true ∧
    work0681.jac.invOK = true ∧ acceptsUnitSq work0681.out = true := by
  norm_num [work0681, contact0681, tau0681, center0681, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0681 : CellCertificate where
  tauBall := tau0681
  contactCenter := center0681
  contactBall := contact0681
  work := work0681
  center_sq := center_sq0681
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0681.1
  jac_ok := checks0681.2.1
  accepted := checks0681.2.2

def tau0682 : RatBall :=
  ⟨⟨43/160, -7/32⟩, 3/320⟩
def center0682 : GaussianRat :=
  ⟨9509069/50000000, -71308977/500000000⟩
def contact0682 : RatBall := localContactBall tau0682 center0682
def work0682 : RoundedTauEval :=
  evalTau precision tau0682 contact0682 logTwoBall

theorem center_sq0682 : (center0682.re : ℝ)^2 +
    (center0682.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0682]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0682 : work0682.theta.ok = true ∧
    work0682.jac.invOK = true ∧ acceptsUnitSq work0682.out = true := by
  norm_num [work0682, contact0682, tau0682, center0682, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0682 : CellCertificate where
  tauBall := tau0682
  contactCenter := center0682
  contactBall := contact0682
  work := work0682
  center_sq := center_sq0682
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0682.1
  jac_ok := checks0682.2.1
  accepted := checks0682.2.2

def tau0683 : RatBall :=
  ⟨⟨41/160, -33/160⟩, 3/320⟩
def center0683 : GaussianRat :=
  ⟨180884951/1000000000, -135214257/1000000000⟩
def contact0683 : RatBall := localContactBall tau0683 center0683
def work0683 : RoundedTauEval :=
  evalTau precision tau0683 contact0683 logTwoBall

theorem center_sq0683 : (center0683.re : ℝ)^2 +
    (center0683.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0683]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0683 : work0683.theta.ok = true ∧
    work0683.jac.invOK = true ∧ acceptsUnitSq work0683.out = true := by
  norm_num [work0683, contact0683, tau0683, center0683, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0683 : CellCertificate where
  tauBall := tau0683
  contactCenter := center0683
  contactBall := contact0683
  work := work0683
  center_sq := center_sq0683
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0683.1
  jac_ok := checks0683.2.1
  accepted := checks0683.2.2

def tau0684 : RatBall :=
  ⟨⟨43/160, -33/160⟩, 3/320⟩
def center0684 : GaussianRat :=
  ⟨189219451/1000000000, -67150009/500000000⟩
def contact0684 : RatBall := localContactBall tau0684 center0684
def work0684 : RoundedTauEval :=
  evalTau precision tau0684 contact0684 logTwoBall

theorem center_sq0684 : (center0684.re : ℝ)^2 +
    (center0684.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0684]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0684 : work0684.theta.ok = true ∧
    work0684.jac.invOK = true ∧ acceptsUnitSq work0684.out = true := by
  norm_num [work0684, contact0684, tau0684, center0684, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0684 : CellCertificate where
  tauBall := tau0684
  contactCenter := center0684
  contactBall := contact0684
  work := work0684
  center_sq := center_sq0684
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0684.1
  jac_ok := checks0684.2.1
  accepted := checks0684.2.2

def tau0685 : RatBall :=
  ⟨⟨9/32, -7/32⟩, 3/320⟩
def center0685 : GaussianRat :=
  ⟨49620407/250000000, -141607653/1000000000⟩
def contact0685 : RatBall := localContactBall tau0685 center0685
def work0685 : RoundedTauEval :=
  evalTau precision tau0685 contact0685 logTwoBall

theorem center_sq0685 : (center0685.re : ℝ)^2 +
    (center0685.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0685]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0685 : work0685.theta.ok = true ∧
    work0685.jac.invOK = true ∧ acceptsUnitSq work0685.out = true := by
  norm_num [work0685, contact0685, tau0685, center0685, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0685 : CellCertificate where
  tauBall := tau0685
  contactCenter := center0685
  contactBall := contact0685
  work := work0685
  center_sq := center_sq0685
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0685.1
  jac_ok := checks0685.2.1
  accepted := checks0685.2.2

def tau0686 : RatBall :=
  ⟨⟨47/160, -7/32⟩, 3/320⟩
def center0686 : GaussianRat :=
  ⟨206714057/1000000000, -70283583/500000000⟩
def contact0686 : RatBall := localContactBall tau0686 center0686
def work0686 : RoundedTauEval :=
  evalTau precision tau0686 contact0686 logTwoBall

theorem center_sq0686 : (center0686.re : ℝ)^2 +
    (center0686.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0686]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0686 : work0686.theta.ok = true ∧
    work0686.jac.invOK = true ∧ acceptsUnitSq work0686.out = true := by
  norm_num [work0686, contact0686, tau0686, center0686, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0686 : CellCertificate where
  tauBall := tau0686
  contactCenter := center0686
  contactBall := contact0686
  work := work0686
  center_sq := center_sq0686
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0686.1
  jac_ok := checks0686.2.1
  accepted := checks0686.2.2

def tau0687 : RatBall :=
  ⟨⟨9/32, -33/160⟩, 3/320⟩
def center0687 : GaussianRat :=
  ⟨197489591/1000000000, -66677907/500000000⟩
def contact0687 : RatBall := localContactBall tau0687 center0687
def work0687 : RoundedTauEval :=
  evalTau precision tau0687 contact0687 logTwoBall

theorem center_sq0687 : (center0687.re : ℝ)^2 +
    (center0687.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0687]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0687 : work0687.theta.ok = true ∧
    work0687.jac.invOK = true ∧ acceptsUnitSq work0687.out = true := by
  norm_num [work0687, contact0687, tau0687, center0687, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0687 : CellCertificate where
  tauBall := tau0687
  contactCenter := center0687
  contactBall := contact0687
  work := work0687
  center_sq := center_sq0687
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0687.1
  jac_ok := checks0687.2.1
  accepted := checks0687.2.2

def cells : List CellCertificate := [cell0680, cell0681, cell0682, cell0683, cell0684, cell0685, cell0686, cell0687]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085
