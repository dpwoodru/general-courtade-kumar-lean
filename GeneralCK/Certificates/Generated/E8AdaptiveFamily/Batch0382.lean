import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3056 : RatBall :=
  ⟨⟨67/640, -243/640⟩, 3/1280⟩
def center3056 : GaussianRat :=
  ⟨42344767/500000000, -273575317/1000000000⟩
def contact3056 : RatBall := localContactBall tau3056 center3056
def work3056 : RoundedTauEval :=
  evalTau precision tau3056 contact3056 logTwoBall

theorem center_sq3056 : (center3056.re : ℝ)^2 +
    (center3056.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3056]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3056 : work3056.theta.ok = true ∧
    work3056.jac.invOK = true ∧ acceptsUnitSq work3056.out = true := by
  norm_num [work3056, contact3056, tau3056, center3056, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3056 : CellCertificate where
  tauBall := tau3056
  contactCenter := center3056
  contactBall := contact3056
  work := work3056
  center_sq := center_sq3056
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3056.1
  jac_ok := checks3056.2.1
  accepted := checks3056.2.2

def tau3057 : RatBall :=
  ⟨⟨13/128, -241/640⟩, 3/1280⟩
def center3057 : GaussianRat :=
  ⟨40983659/500000000, -135659503/500000000⟩
def contact3057 : RatBall := localContactBall tau3057 center3057
def work3057 : RoundedTauEval :=
  evalTau precision tau3057 contact3057 logTwoBall

theorem center_sq3057 : (center3057.re : ℝ)^2 +
    (center3057.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3057]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3057 : work3057.theta.ok = true ∧
    work3057.jac.invOK = true ∧ acceptsUnitSq work3057.out = true := by
  norm_num [work3057, contact3057, tau3057, center3057, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3057 : CellCertificate where
  tauBall := tau3057
  contactCenter := center3057
  contactBall := contact3057
  work := work3057
  center_sq := center_sq3057
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3057.1
  jac_ok := checks3057.2.1
  accepted := checks3057.2.2

def tau3058 : RatBall :=
  ⟨⟨67/640, -241/640⟩, 3/1280⟩
def center3058 : GaussianRat :=
  ⟨84453299/1000000000, -5421753/20000000⟩
def contact3058 : RatBall := localContactBall tau3058 center3058
def work3058 : RoundedTauEval :=
  evalTau precision tau3058 contact3058 logTwoBall

theorem center_sq3058 : (center3058.re : ℝ)^2 +
    (center3058.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3058]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3058 : work3058.theta.ok = true ∧
    work3058.jac.invOK = true ∧ acceptsUnitSq work3058.out = true := by
  norm_num [work3058, contact3058, tau3058, center3058, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3058 : CellCertificate where
  tauBall := tau3058
  contactCenter := center3058
  contactBall := contact3058
  work := work3058
  center_sq := center_sq3058
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3058.1
  jac_ok := checks3058.2.1
  accepted := checks3058.2.2

def tau3059 : RatBall :=
  ⟨⟨69/640, -243/640⟩, 3/1280⟩
def center3059 : GaussianRat :=
  ⟨87178851/1000000000, -273334167/1000000000⟩
def contact3059 : RatBall := localContactBall tau3059 center3059
def work3059 : RoundedTauEval :=
  evalTau precision tau3059 contact3059 logTwoBall

theorem center_sq3059 : (center3059.re : ℝ)^2 +
    (center3059.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3059]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3059 : work3059.theta.ok = true ∧
    work3059.jac.invOK = true ∧ acceptsUnitSq work3059.out = true := by
  norm_num [work3059, contact3059, tau3059, center3059, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3059 : CellCertificate where
  tauBall := tau3059
  contactCenter := center3059
  contactBall := contact3059
  work := work3059
  center_sq := center_sq3059
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3059.1
  jac_ok := checks3059.2.1
  accepted := checks3059.2.2

def tau3060 : RatBall :=
  ⟨⟨71/640, -243/640⟩, 3/1280⟩
def center3060 : GaussianRat :=
  ⟨89664833/1000000000, -68271613/250000000⟩
def contact3060 : RatBall := localContactBall tau3060 center3060
def work3060 : RoundedTauEval :=
  evalTau precision tau3060 contact3060 logTwoBall

theorem center_sq3060 : (center3060.re : ℝ)^2 +
    (center3060.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3060]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3060 : work3060.theta.ok = true ∧
    work3060.jac.invOK = true ∧ acceptsUnitSq work3060.out = true := by
  norm_num [work3060, contact3060, tau3060, center3060, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3060 : CellCertificate where
  tauBall := tau3060
  contactCenter := center3060
  contactBall := contact3060
  work := work3060
  center_sq := center_sq3060
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3060.1
  jac_ok := checks3060.2.1
  accepted := checks3060.2.2

def tau3061 : RatBall :=
  ⟨⟨69/640, -241/640⟩, 3/1280⟩
def center3061 : GaussianRat :=
  ⟨10867009/125000000, -67712443/250000000⟩
def contact3061 : RatBall := localContactBall tau3061 center3061
def work3061 : RoundedTauEval :=
  evalTau precision tau3061 contact3061 logTwoBall

theorem center_sq3061 : (center3061.re : ℝ)^2 +
    (center3061.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3061]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3061 : work3061.theta.ok = true ∧
    work3061.jac.invOK = true ∧ acceptsUnitSq work3061.out = true := by
  norm_num [work3061, contact3061, tau3061, center3061, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3061 : CellCertificate where
  tauBall := tau3061
  contactCenter := center3061
  contactBall := contact3061
  work := work3061
  center_sq := center_sq3061
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3061.1
  jac_ok := checks3061.2.1
  accepted := checks3061.2.2

def tau3062 : RatBall :=
  ⟨⟨71/640, -241/640⟩, 3/1280⟩
def center3062 : GaussianRat :=
  ⟨89415553/1000000000, -270605413/1000000000⟩
def contact3062 : RatBall := localContactBall tau3062 center3062
def work3062 : RoundedTauEval :=
  evalTau precision tau3062 contact3062 logTwoBall

theorem center_sq3062 : (center3062.re : ℝ)^2 +
    (center3062.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3062]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3062 : work3062.theta.ok = true ∧
    work3062.jac.invOK = true ∧ acceptsUnitSq work3062.out = true := by
  norm_num [work3062, contact3062, tau3062, center3062, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3062 : CellCertificate where
  tauBall := tau3062
  contactCenter := center3062
  contactBall := contact3062
  work := work3062
  center_sq := center_sq3062
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3062.1
  jac_ok := checks3062.2.1
  accepted := checks3062.2.2

def tau3063 : RatBall :=
  ⟨⟨73/640, -49/128⟩, 3/1280⟩
def center3063 : GaussianRat :=
  ⟨92406637/1000000000, -275316291/1000000000⟩
def contact3063 : RatBall := localContactBall tau3063 center3063
def work3063 : RoundedTauEval :=
  evalTau precision tau3063 contact3063 logTwoBall

theorem center_sq3063 : (center3063.re : ℝ)^2 +
    (center3063.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3063]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3063 : work3063.theta.ok = true ∧
    work3063.jac.invOK = true ∧ acceptsUnitSq work3063.out = true := by
  norm_num [work3063, contact3063, tau3063, center3063, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3063 : CellCertificate where
  tauBall := tau3063
  contactCenter := center3063
  contactBall := contact3063
  work := work3063
  center_sq := center_sq3063
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3063.1
  jac_ok := checks3063.2.1
  accepted := checks3063.2.2

def cells : List CellCertificate := [cell3056, cell3057, cell3058, cell3059, cell3060, cell3061, cell3062, cell3063]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382
