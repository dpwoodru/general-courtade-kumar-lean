import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3112 : RatBall :=
  ⟨⟨87/640, -233/640⟩, 3/1280⟩
def center3112 : GaussianRat :=
  ⟨10796407/100000000, -129338763/500000000⟩
def contact3112 : RatBall := localContactBall tau3112 center3112
def work3112 : RoundedTauEval :=
  evalTau precision tau3112 contact3112 logTwoBall

theorem center_sq3112 : (center3112.re : ℝ)^2 +
    (center3112.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3112]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3112 : work3112.theta.ok = true ∧
    work3112.jac.invOK = true ∧ acceptsUnitSq work3112.out = true := by
  norm_num [work3112, contact3112, tau3112, center3112, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3112 : CellCertificate where
  tauBall := tau3112
  contactCenter := center3112
  contactBall := contact3112
  work := work3112
  center_sq := center_sq3112
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3112.1
  jac_ok := checks3112.2.1
  accepted := checks3112.2.2

def tau3113 : RatBall :=
  ⟨⟨89/640, -239/640⟩, 3/1280⟩
def center3113 : GaussianRat :=
  ⟨111267493/1000000000, -265680799/1000000000⟩
def contact3113 : RatBall := localContactBall tau3113 center3113
def work3113 : RoundedTauEval :=
  evalTau precision tau3113 contact3113 logTwoBall

theorem center_sq3113 : (center3113.re : ℝ)^2 +
    (center3113.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3113]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3113 : work3113.theta.ok = true ∧
    work3113.jac.invOK = true ∧ acceptsUnitSq work3113.out = true := by
  norm_num [work3113, contact3113, tau3113, center3113, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3113 : CellCertificate where
  tauBall := tau3113
  contactCenter := center3113
  contactBall := contact3113
  work := work3113
  center_sq := center_sq3113
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3113.1
  jac_ok := checks3113.2.1
  accepted := checks3113.2.2

def tau3114 : RatBall :=
  ⟨⟨91/640, -239/640⟩, 3/1280⟩
def center3114 : GaussianRat :=
  ⟨113703619/1000000000, -265378247/1000000000⟩
def contact3114 : RatBall := localContactBall tau3114 center3114
def work3114 : RoundedTauEval :=
  evalTau precision tau3114 contact3114 logTwoBall

theorem center_sq3114 : (center3114.re : ℝ)^2 +
    (center3114.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3114]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3114 : work3114.theta.ok = true ∧
    work3114.jac.invOK = true ∧ acceptsUnitSq work3114.out = true := by
  norm_num [work3114, contact3114, tau3114, center3114, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3114 : CellCertificate where
  tauBall := tau3114
  contactCenter := center3114
  contactBall := contact3114
  work := work3114
  center_sq := center_sq3114
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3114.1
  jac_ok := checks3114.2.1
  accepted := checks3114.2.2

def tau3115 : RatBall :=
  ⟨⟨89/640, -237/640⟩, 3/1280⟩
def center3115 : GaussianRat :=
  ⟨55484957/500000000, -65811399/250000000⟩
def contact3115 : RatBall := localContactBall tau3115 center3115
def work3115 : RoundedTauEval :=
  evalTau precision tau3115 contact3115 logTwoBall

theorem center_sq3115 : (center3115.re : ℝ)^2 +
    (center3115.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3115]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3115 : work3115.theta.ok = true ∧
    work3115.jac.invOK = true ∧ acceptsUnitSq work3115.out = true := by
  norm_num [work3115, contact3115, tau3115, center3115, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3115 : CellCertificate where
  tauBall := tau3115
  contactCenter := center3115
  contactBall := contact3115
  work := work3115
  center_sq := center_sq3115
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3115.1
  jac_ok := checks3115.2.1
  accepted := checks3115.2.2

def tau3116 : RatBall :=
  ⟨⟨91/640, -237/640⟩, 3/1280⟩
def center3116 : GaussianRat :=
  ⟨22680033/200000000, -131473549/500000000⟩
def contact3116 : RatBall := localContactBall tau3116 center3116
def work3116 : RoundedTauEval :=
  evalTau precision tau3116 contact3116 logTwoBall

theorem center_sq3116 : (center3116.re : ℝ)^2 +
    (center3116.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3116]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3116 : work3116.theta.ok = true ∧
    work3116.jac.invOK = true ∧ acceptsUnitSq work3116.out = true := by
  norm_num [work3116, contact3116, tau3116, center3116, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3116 : CellCertificate where
  tauBall := tau3116
  contactCenter := center3116
  contactBall := contact3116
  work := work3116
  center_sq := center_sq3116
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3116.1
  jac_ok := checks3116.2.1
  accepted := checks3116.2.2

def tau3117 : RatBall :=
  ⟨⟨93/640, -239/640⟩, 3/1280⟩
def center3117 : GaussianRat :=
  ⟨116135629/1000000000, -265069807/1000000000⟩
def contact3117 : RatBall := localContactBall tau3117 center3117
def work3117 : RoundedTauEval :=
  evalTau precision tau3117 contact3117 logTwoBall

theorem center_sq3117 : (center3117.re : ℝ)^2 +
    (center3117.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3117]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3117 : work3117.theta.ok = true ∧
    work3117.jac.invOK = true ∧ acceptsUnitSq work3117.out = true := by
  norm_num [work3117, contact3117, tau3117, center3117, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3117 : CellCertificate where
  tauBall := tau3117
  contactCenter := center3117
  contactBall := contact3117
  work := work3117
  center_sq := center_sq3117
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3117.1
  jac_ok := checks3117.2.1
  accepted := checks3117.2.2

def tau3118 : RatBall :=
  ⟨⟨19/128, -239/640⟩, 3/1280⟩
def center3118 : GaussianRat :=
  ⟨118563451/1000000000, -66188883/250000000⟩
def contact3118 : RatBall := localContactBall tau3118 center3118
def work3118 : RoundedTauEval :=
  evalTau precision tau3118 contact3118 logTwoBall

theorem center_sq3118 : (center3118.re : ℝ)^2 +
    (center3118.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3118]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3118 : work3118.theta.ok = true ∧
    work3118.jac.invOK = true ∧ acceptsUnitSq work3118.out = true := by
  norm_num [work3118, contact3118, tau3118, center3118, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3118 : CellCertificate where
  tauBall := tau3118
  contactCenter := center3118
  contactBall := contact3118
  work := work3118
  center_sq := center_sq3118
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3118.1
  jac_ok := checks3118.2.1
  accepted := checks3118.2.2

def tau3119 : RatBall :=
  ⟨⟨93/640, -237/640⟩, 3/1280⟩
def center3119 : GaussianRat :=
  ⟨115826349/1000000000, -52528557/200000000⟩
def contact3119 : RatBall := localContactBall tau3119 center3119
def work3119 : RoundedTauEval :=
  evalTau precision tau3119 contact3119 logTwoBall

theorem center_sq3119 : (center3119.re : ℝ)^2 +
    (center3119.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3119]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3119 : work3119.theta.ok = true ∧
    work3119.jac.invOK = true ∧ acceptsUnitSq work3119.out = true := by
  norm_num [work3119, contact3119, tau3119, center3119, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3119 : CellCertificate where
  tauBall := tau3119
  contactCenter := center3119
  contactBall := contact3119
  work := work3119
  center_sq := center_sq3119
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3119.1
  jac_ok := checks3119.2.1
  accepted := checks3119.2.2

def cells : List CellCertificate := [cell3112, cell3113, cell3114, cell3115, cell3116, cell3117, cell3118, cell3119]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389
