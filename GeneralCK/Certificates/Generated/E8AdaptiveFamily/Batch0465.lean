import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0465

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3720 : RatBall :=
  ⟨⟨87/640, 233/640⟩, 3/1280⟩
def center3720 : GaussianRat :=
  ⟨10796407/100000000, 129338763/500000000⟩
def contact3720 : RatBall := localContactBall tau3720 center3720
def work3720 : RoundedTauEval :=
  evalTau precision tau3720 contact3720 logTwoBall

theorem center_sq3720 : (center3720.re : ℝ)^2 +
    (center3720.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3720]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3720 : work3720.theta.ok = true ∧
    work3720.jac.invOK = true ∧ acceptsUnitSq work3720.out = true := by
  norm_num [work3720, contact3720, tau3720, center3720, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3720 : CellCertificate where
  tauBall := tau3720
  contactCenter := center3720
  contactBall := contact3720
  work := work3720
  center_sq := center_sq3720
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3720.1
  jac_ok := checks3720.2.1
  accepted := checks3720.2.2

def tau3721 : RatBall :=
  ⟨⟨17/128, 47/128⟩, 3/1280⟩
def center3721 : GaussianRat :=
  ⟨13226959/125000000, 130693913/500000000⟩
def contact3721 : RatBall := localContactBall tau3721 center3721
def work3721 : RoundedTauEval :=
  evalTau precision tau3721 contact3721 logTwoBall

theorem center_sq3721 : (center3721.re : ℝ)^2 +
    (center3721.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3721]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3721 : work3721.theta.ok = true ∧
    work3721.jac.invOK = true ∧ acceptsUnitSq work3721.out = true := by
  norm_num [work3721, contact3721, tau3721, center3721, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3721 : CellCertificate where
  tauBall := tau3721
  contactCenter := center3721
  contactBall := contact3721
  work := work3721
  center_sq := center_sq3721
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3721.1
  jac_ok := checks3721.2.1
  accepted := checks3721.2.2

def tau3722 : RatBall :=
  ⟨⟨87/640, 47/128⟩, 3/1280⟩
def center3722 : GaussianRat :=
  ⟨21649587/200000000, 815953/3125000⟩
def contact3722 : RatBall := localContactBall tau3722 center3722
def work3722 : RoundedTauEval :=
  evalTau precision tau3722 contact3722 logTwoBall

theorem center_sq3722 : (center3722.re : ℝ)^2 +
    (center3722.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3722]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3722 : work3722.theta.ok = true ∧
    work3722.jac.invOK = true ∧ acceptsUnitSq work3722.out = true := by
  norm_num [work3722, contact3722, tau3722, center3722, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3722 : CellCertificate where
  tauBall := tau3722
  contactCenter := center3722
  contactBall := contact3722
  work := work3722
  center_sq := center_sq3722
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3722.1
  jac_ok := checks3722.2.1
  accepted := checks3722.2.2

def tau3723 : RatBall :=
  ⟨⟨81/640, 237/640⟩, 3/1280⟩
def center3723 : GaussianRat :=
  ⟨101209731/1000000000, 10575219/40000000⟩
def contact3723 : RatBall := localContactBall tau3723 center3723
def work3723 : RoundedTauEval :=
  evalTau precision tau3723 contact3723 logTwoBall

theorem center_sq3723 : (center3723.re : ℝ)^2 +
    (center3723.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3723]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3723 : work3723.theta.ok = true ∧
    work3723.jac.invOK = true ∧ acceptsUnitSq work3723.out = true := by
  norm_num [work3723, contact3723, tau3723, center3723, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3723 : CellCertificate where
  tauBall := tau3723
  contactCenter := center3723
  contactBall := contact3723
  work := work3723
  center_sq := center_sq3723
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3723.1
  jac_ok := checks3723.2.1
  accepted := checks3723.2.2

def tau3724 : RatBall :=
  ⟨⟨83/640, 237/640⟩, 3/1280⟩
def center3724 : GaussianRat :=
  ⟨6478469/62500000, 132052859/500000000⟩
def contact3724 : RatBall := localContactBall tau3724 center3724
def work3724 : RoundedTauEval :=
  evalTau precision tau3724 contact3724 logTwoBall

theorem center_sq3724 : (center3724.re : ℝ)^2 +
    (center3724.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3724]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3724 : work3724.theta.ok = true ∧
    work3724.jac.invOK = true ∧ acceptsUnitSq work3724.out = true := by
  norm_num [work3724, contact3724, tau3724, center3724, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3724 : CellCertificate where
  tauBall := tau3724
  contactCenter := center3724
  contactBall := contact3724
  work := work3724
  center_sq := center_sq3724
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3724.1
  jac_ok := checks3724.2.1
  accepted := checks3724.2.2

def tau3725 : RatBall :=
  ⟨⟨81/640, 239/640⟩, 3/1280⟩
def center3725 : GaussianRat :=
  ⟨50741661/500000000, 53366229/200000000⟩
def contact3725 : RatBall := localContactBall tau3725 center3725
def work3725 : RoundedTauEval :=
  evalTau precision tau3725 contact3725 logTwoBall

theorem center_sq3725 : (center3725.re : ℝ)^2 +
    (center3725.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3725]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3725 : work3725.theta.ok = true ∧
    work3725.jac.invOK = true ∧ acceptsUnitSq work3725.out = true := by
  norm_num [work3725, contact3725, tau3725, center3725, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3725 : CellCertificate where
  tauBall := tau3725
  contactCenter := center3725
  contactBall := contact3725
  work := work3725
  center_sq := center_sq3725
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3725.1
  jac_ok := checks3725.2.1
  accepted := checks3725.2.2

def tau3726 : RatBall :=
  ⟨⟨83/640, 239/640⟩, 3/1280⟩
def center3726 : GaussianRat :=
  ⟨103935163/1000000000, 66638159/250000000⟩
def contact3726 : RatBall := localContactBall tau3726 center3726
def work3726 : RoundedTauEval :=
  evalTau precision tau3726 contact3726 logTwoBall

theorem center_sq3726 : (center3726.re : ℝ)^2 +
    (center3726.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3726]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3726 : work3726.theta.ok = true ∧
    work3726.jac.invOK = true ∧ acceptsUnitSq work3726.out = true := by
  norm_num [work3726, contact3726, tau3726, center3726, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3726 : CellCertificate where
  tauBall := tau3726
  contactCenter := center3726
  contactBall := contact3726
  work := work3726
  center_sq := center_sq3726
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3726.1
  jac_ok := checks3726.2.1
  accepted := checks3726.2.2

def tau3727 : RatBall :=
  ⟨⟨17/128, 237/640⟩, 3/1280⟩
def center3727 : GaussianRat :=
  ⟨106097509/1000000000, 131912477/500000000⟩
def contact3727 : RatBall := localContactBall tau3727 center3727
def work3727 : RoundedTauEval :=
  evalTau precision tau3727 contact3727 logTwoBall

theorem center_sq3727 : (center3727.re : ℝ)^2 +
    (center3727.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3727]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3727 : work3727.theta.ok = true ∧
    work3727.jac.invOK = true ∧ acceptsUnitSq work3727.out = true := by
  norm_num [work3727, contact3727, tau3727, center3727, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3727 : CellCertificate where
  tauBall := tau3727
  contactCenter := center3727
  contactBall := contact3727
  work := work3727
  center_sq := center_sq3727
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3727.1
  jac_ok := checks3727.2.1
  accepted := checks3727.2.2

def cells : List CellCertificate := [cell3720, cell3721, cell3722, cell3723, cell3724, cell3725, cell3726, cell3727]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0465
