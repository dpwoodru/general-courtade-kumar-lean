import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3032 : RatBall :=
  ⟨⟨59/640, -247/640⟩, 3/1280⟩
def center3032 : GaussianRat :=
  ⟨75128671/1000000000, -55898717/200000000⟩
def contact3032 : RatBall := localContactBall tau3032 center3032
def work3032 : RoundedTauEval :=
  evalTau precision tau3032 contact3032 logTwoBall

theorem center_sq3032 : (center3032.re : ℝ)^2 +
    (center3032.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3032]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3032 : work3032.theta.ok = true ∧
    work3032.jac.invOK = true ∧ acceptsUnitSq work3032.out = true := by
  norm_num [work3032, contact3032, tau3032, center3032, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3032 : CellCertificate where
  tauBall := tau3032
  contactCenter := center3032
  contactBall := contact3032
  work := work3032
  center_sq := center_sq3032
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3032.1
  jac_ok := checks3032.2.1
  accepted := checks3032.2.2

def tau3033 : RatBall :=
  ⟨⟨57/640, -49/128⟩, 3/1280⟩
def center3033 : GaussianRat :=
  ⟨7240167/100000000, -277190643/1000000000⟩
def contact3033 : RatBall := localContactBall tau3033 center3033
def work3033 : RoundedTauEval :=
  evalTau precision tau3033 contact3033 logTwoBall

theorem center_sq3033 : (center3033.re : ℝ)^2 +
    (center3033.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3033]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3033 : work3033.theta.ok = true ∧
    work3033.jac.invOK = true ∧ acceptsUnitSq work3033.out = true := by
  norm_num [work3033, contact3033, tau3033, center3033, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3033 : CellCertificate where
  tauBall := tau3033
  contactCenter := center3033
  contactBall := contact3033
  work := work3033
  center_sq := center_sq3033
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3033.1
  jac_ok := checks3033.2.1
  accepted := checks3033.2.2

def tau3034 : RatBall :=
  ⟨⟨59/640, -49/128⟩, 3/1280⟩
def center3034 : GaussianRat :=
  ⟨7491319/100000000, -34622509/125000000⟩
def contact3034 : RatBall := localContactBall tau3034 center3034
def work3034 : RoundedTauEval :=
  evalTau precision tau3034 contact3034 logTwoBall

theorem center_sq3034 : (center3034.re : ℝ)^2 +
    (center3034.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3034]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3034 : work3034.theta.ok = true ∧
    work3034.jac.invOK = true ∧ acceptsUnitSq work3034.out = true := by
  norm_num [work3034, contact3034, tau3034, center3034, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3034 : CellCertificate where
  tauBall := tau3034
  contactCenter := center3034
  contactBall := contact3034
  work := work3034
  center_sq := center_sq3034
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3034.1
  jac_ok := checks3034.2.1
  accepted := checks3034.2.2

def tau3035 : RatBall :=
  ⟨⟨61/640, -247/640⟩, 3/1280⟩
def center3035 : GaussianRat :=
  ⟨77644141/1000000000, -139636577/500000000⟩
def contact3035 : RatBall := localContactBall tau3035 center3035
def work3035 : RoundedTauEval :=
  evalTau precision tau3035 contact3035 logTwoBall

theorem center_sq3035 : (center3035.re : ℝ)^2 +
    (center3035.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3035]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3035 : work3035.theta.ok = true ∧
    work3035.jac.invOK = true ∧ acceptsUnitSq work3035.out = true := by
  norm_num [work3035, contact3035, tau3035, center3035, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3035 : CellCertificate where
  tauBall := tau3035
  contactCenter := center3035
  contactBall := contact3035
  work := work3035
  center_sq := center_sq3035
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3035.1
  jac_ok := checks3035.2.1
  accepted := checks3035.2.2

def tau3036 : RatBall :=
  ⟨⟨63/640, -247/640⟩, 3/1280⟩
def center3036 : GaussianRat :=
  ⟨40078273/500000000, -69761453/250000000⟩
def contact3036 : RatBall := localContactBall tau3036 center3036
def work3036 : RoundedTauEval :=
  evalTau precision tau3036 contact3036 logTwoBall

theorem center_sq3036 : (center3036.re : ℝ)^2 +
    (center3036.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3036]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3036 : work3036.theta.ok = true ∧
    work3036.jac.invOK = true ∧ acceptsUnitSq work3036.out = true := by
  norm_num [work3036, contact3036, tau3036, center3036, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3036 : CellCertificate where
  tauBall := tau3036
  contactCenter := center3036
  contactBall := contact3036
  work := work3036
  center_sq := center_sq3036
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3036.1
  jac_ok := checks3036.2.1
  accepted := checks3036.2.2

def tau3037 : RatBall :=
  ⟨⟨61/640, -49/128⟩, 3/1280⟩
def center3037 : GaussianRat :=
  ⟨3096871/40000000, -138381321/500000000⟩
def contact3037 : RatBall := localContactBall tau3037 center3037
def work3037 : RoundedTauEval :=
  evalTau precision tau3037 contact3037 logTwoBall

theorem center_sq3037 : (center3037.re : ℝ)^2 +
    (center3037.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3037]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3037 : work3037.theta.ok = true ∧
    work3037.jac.invOK = true ∧ acceptsUnitSq work3037.out = true := by
  norm_num [work3037, contact3037, tau3037, center3037, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3037 : CellCertificate where
  tauBall := tau3037
  contactCenter := center3037
  contactBall := contact3037
  work := work3037
  center_sq := center_sq3037
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3037.1
  jac_ok := checks3037.2.1
  accepted := checks3037.2.2

def tau3038 : RatBall :=
  ⟨⟨63/640, -49/128⟩, 3/1280⟩
def center3038 : GaussianRat :=
  ⟨39963667/500000000, -276538391/1000000000⟩
def contact3038 : RatBall := localContactBall tau3038 center3038
def work3038 : RoundedTauEval :=
  evalTau precision tau3038 contact3038 logTwoBall

theorem center_sq3038 : (center3038.re : ℝ)^2 +
    (center3038.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3038]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3038 : work3038.theta.ok = true ∧
    work3038.jac.invOK = true ∧ acceptsUnitSq work3038.out = true := by
  norm_num [work3038, contact3038, tau3038, center3038, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3038 : CellCertificate where
  tauBall := tau3038
  contactCenter := center3038
  contactBall := contact3038
  work := work3038
  center_sq := center_sq3038
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3038.1
  jac_ok := checks3038.2.1
  accepted := checks3038.2.2

def tau3039 : RatBall :=
  ⟨⟨57/640, -243/640⟩, 3/1280⟩
def center3039 : GaussianRat :=
  ⟨72195957/1000000000, -1716757/6250000⟩
def contact3039 : RatBall := localContactBall tau3039 center3039
def work3039 : RoundedTauEval :=
  evalTau precision tau3039 contact3039 logTwoBall

theorem center_sq3039 : (center3039.re : ℝ)^2 +
    (center3039.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3039 : work3039.theta.ok = true ∧
    work3039.jac.invOK = true ∧ acceptsUnitSq work3039.out = true := by
  norm_num [work3039, contact3039, tau3039, center3039, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3039 : CellCertificate where
  tauBall := tau3039
  contactCenter := center3039
  contactBall := contact3039
  work := work3039
  center_sq := center_sq3039
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3039.1
  jac_ok := checks3039.2.1
  accepted := checks3039.2.2

def cells : List CellCertificate := [cell3032, cell3033, cell3034, cell3035, cell3036, cell3037, cell3038, cell3039]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379
