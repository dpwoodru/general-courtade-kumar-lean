import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0077

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0616 : RatBall :=
  ⟨⟨17/160, -41/160⟩, 3/320⟩
def center0616 : GaussianRat :=
  ⟨1572299/20000000, -179469913/1000000000⟩
def contact0616 : RatBall := localContactBall tau0616 center0616
def work0616 : RoundedTauEval :=
  evalTau precision tau0616 contact0616 logTwoBall

theorem center_sq0616 : (center0616.re : ℝ)^2 +
    (center0616.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0616]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0616 : work0616.theta.ok = true ∧
    work0616.jac.invOK = true ∧ acceptsUnitSq work0616.out = true := by
  norm_num [work0616, contact0616, tau0616, center0616, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0616 : CellCertificate where
  tauBall := tau0616
  contactCenter := center0616
  contactBall := contact0616
  work := work0616
  center_sq := center_sq0616
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0616.1
  jac_ok := checks0616.2.1
  accepted := checks0616.2.2

def tau0617 : RatBall :=
  ⟨⟨19/160, -41/160⟩, 3/320⟩
def center0617 : GaussianRat :=
  ⟨43873979/500000000, -35778323/200000000⟩
def contact0617 : RatBall := localContactBall tau0617 center0617
def work0617 : RoundedTauEval :=
  evalTau precision tau0617 contact0617 logTwoBall

theorem center_sq0617 : (center0617.re : ℝ)^2 +
    (center0617.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0617]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0617 : work0617.theta.ok = true ∧
    work0617.jac.invOK = true ∧ acceptsUnitSq work0617.out = true := by
  norm_num [work0617, contact0617, tau0617, center0617, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0617 : CellCertificate where
  tauBall := tau0617
  contactCenter := center0617
  contactBall := contact0617
  work := work0617
  center_sq := center_sq0617
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0617.1
  jac_ok := checks0617.2.1
  accepted := checks0617.2.2

def tau0618 : RatBall :=
  ⟨⟨21/160, -43/160⟩, 3/320⟩
def center0618 : GaussianRat :=
  ⟨1523927/15625000, -46839637/250000000⟩
def contact0618 : RatBall := localContactBall tau0618 center0618
def work0618 : RoundedTauEval :=
  evalTau precision tau0618 contact0618 logTwoBall

theorem center_sq0618 : (center0618.re : ℝ)^2 +
    (center0618.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0618]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0618 : work0618.theta.ok = true ∧
    work0618.jac.invOK = true ∧ acceptsUnitSq work0618.out = true := by
  norm_num [work0618, contact0618, tau0618, center0618, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0618 : CellCertificate where
  tauBall := tau0618
  contactCenter := center0618
  contactBall := contact0618
  work := work0618
  center_sq := center_sq0618
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0618.1
  jac_ok := checks0618.2.1
  accepted := checks0618.2.2

def tau0619 : RatBall :=
  ⟨⟨23/160, -43/160⟩, 3/320⟩
def center0619 : GaussianRat :=
  ⟨106644393/1000000000, -93309307/500000000⟩
def contact0619 : RatBall := localContactBall tau0619 center0619
def work0619 : RoundedTauEval :=
  evalTau precision tau0619 contact0619 logTwoBall

theorem center_sq0619 : (center0619.re : ℝ)^2 +
    (center0619.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0619]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0619 : work0619.theta.ok = true ∧
    work0619.jac.invOK = true ∧ acceptsUnitSq work0619.out = true := by
  norm_num [work0619, contact0619, tau0619, center0619, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0619 : CellCertificate where
  tauBall := tau0619
  contactCenter := center0619
  contactBall := contact0619
  work := work0619
  center_sq := center_sq0619
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0619.1
  jac_ok := checks0619.2.1
  accepted := checks0619.2.2

def tau0620 : RatBall :=
  ⟨⟨21/160, -41/160⟩, 3/320⟩
def center0620 : GaussianRat :=
  ⟨96843181/1000000000, -5570429/31250000⟩
def contact0620 : RatBall := localContactBall tau0620 center0620
def work0620 : RoundedTauEval :=
  evalTau precision tau0620 contact0620 logTwoBall

theorem center_sq0620 : (center0620.re : ℝ)^2 +
    (center0620.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0620]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0620 : work0620.theta.ok = true ∧
    work0620.jac.invOK = true ∧ acceptsUnitSq work0620.out = true := by
  norm_num [work0620, contact0620, tau0620, center0620, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0620 : CellCertificate where
  tauBall := tau0620
  contactCenter := center0620
  contactBall := contact0620
  work := work0620
  center_sq := center_sq0620
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0620.1
  jac_ok := checks0620.2.1
  accepted := checks0620.2.2

def tau0621 : RatBall :=
  ⟨⟨23/160, -41/160⟩, 3/320⟩
def center0621 : GaussianRat :=
  ⟨105897059/1000000000, -22194707/125000000⟩
def contact0621 : RatBall := localContactBall tau0621 center0621
def work0621 : RoundedTauEval :=
  evalTau precision tau0621 contact0621 logTwoBall

theorem center_sq0621 : (center0621.re : ℝ)^2 +
    (center0621.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0621]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0621 : work0621.theta.ok = true ∧
    work0621.jac.invOK = true ∧ acceptsUnitSq work0621.out = true := by
  norm_num [work0621, contact0621, tau0621, center0621, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0621 : CellCertificate where
  tauBall := tau0621
  contactCenter := center0621
  contactBall := contact0621
  work := work0621
  center_sq := center_sq0621
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0621.1
  jac_ok := checks0621.2.1
  accepted := checks0621.2.2

def tau0622 : RatBall :=
  ⟨⟨5/32, -47/160⟩, 3/320⟩
def center0622 : GaussianRat :=
  ⟨58736127/500000000, -40804889/200000000⟩
def contact0622 : RatBall := localContactBall tau0622 center0622
def work0622 : RoundedTauEval :=
  evalTau precision tau0622 contact0622 logTwoBall

theorem center_sq0622 : (center0622.re : ℝ)^2 +
    (center0622.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0622]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0622 : work0622.theta.ok = true ∧
    work0622.jac.invOK = true ∧ acceptsUnitSq work0622.out = true := by
  norm_num [work0622, contact0622, tau0622, center0622, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0622 : CellCertificate where
  tauBall := tau0622
  contactCenter := center0622
  contactBall := contact0622
  work := work0622
  center_sq := center_sq0622
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0622.1
  jac_ok := checks0622.2.1
  accepted := checks0622.2.2

def tau0623 : RatBall :=
  ⟨⟨27/160, -47/160⟩, 3/320⟩
def center0623 : GaussianRat :=
  ⟨31652671/250000000, -101529593/500000000⟩
def contact0623 : RatBall := localContactBall tau0623 center0623
def work0623 : RoundedTauEval :=
  evalTau precision tau0623 contact0623 logTwoBall

theorem center_sq0623 : (center0623.re : ℝ)^2 +
    (center0623.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0623]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0623 : work0623.theta.ok = true ∧
    work0623.jac.invOK = true ∧ acceptsUnitSq work0623.out = true := by
  norm_num [work0623, contact0623, tau0623, center0623, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0623 : CellCertificate where
  tauBall := tau0623
  contactCenter := center0623
  contactBall := contact0623
  work := work0623
  center_sq := center_sq0623
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0623.1
  jac_ok := checks0623.2.1
  accepted := checks0623.2.2

def cells : List CellCertificate := [cell0616, cell0617, cell0618, cell0619, cell0620, cell0621, cell0622, cell0623]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0077
