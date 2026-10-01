import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3288 : RatBall :=
  ⟨⟨-93/640, 237/640⟩, 3/1280⟩
def center3288 : GaussianRat :=
  ⟨-115826349/1000000000, 52528557/200000000⟩
def contact3288 : RatBall := localContactBall tau3288 center3288
def work3288 : RoundedTauEval :=
  evalTau precision tau3288 contact3288 logTwoBall

theorem center_sq3288 : (center3288.re : ℝ)^2 +
    (center3288.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3288]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3288 : work3288.theta.ok = true ∧
    work3288.jac.invOK = true ∧ acceptsUnitSq work3288.out = true := by
  norm_num [work3288, contact3288, tau3288, center3288, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3288 : CellCertificate where
  tauBall := tau3288
  contactCenter := center3288
  contactBall := contact3288
  work := work3288
  center_sq := center_sq3288
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3288.1
  jac_ok := checks3288.2.1
  accepted := checks3288.2.2

def tau3289 : RatBall :=
  ⟨⟨-19/128, 239/640⟩, 3/1280⟩
def center3289 : GaussianRat :=
  ⟨-118563451/1000000000, 66188883/250000000⟩
def contact3289 : RatBall := localContactBall tau3289 center3289
def work3289 : RoundedTauEval :=
  evalTau precision tau3289 contact3289 logTwoBall

theorem center_sq3289 : (center3289.re : ℝ)^2 +
    (center3289.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3289]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3289 : work3289.theta.ok = true ∧
    work3289.jac.invOK = true ∧ acceptsUnitSq work3289.out = true := by
  norm_num [work3289, contact3289, tau3289, center3289, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3289 : CellCertificate where
  tauBall := tau3289
  contactCenter := center3289
  contactBall := contact3289
  work := work3289
  center_sq := center_sq3289
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3289.1
  jac_ok := checks3289.2.1
  accepted := checks3289.2.2

def tau3290 : RatBall :=
  ⟨⟨-93/640, 239/640⟩, 3/1280⟩
def center3290 : GaussianRat :=
  ⟨-116135629/1000000000, 265069807/1000000000⟩
def contact3290 : RatBall := localContactBall tau3290 center3290
def work3290 : RoundedTauEval :=
  evalTau precision tau3290 contact3290 logTwoBall

theorem center_sq3290 : (center3290.re : ℝ)^2 +
    (center3290.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3290]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3290 : work3290.theta.ok = true ∧
    work3290.jac.invOK = true ∧ acceptsUnitSq work3290.out = true := by
  norm_num [work3290, contact3290, tau3290, center3290, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3290 : CellCertificate where
  tauBall := tau3290
  contactCenter := center3290
  contactBall := contact3290
  work := work3290
  center_sq := center_sq3290
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3290.1
  jac_ok := checks3290.2.1
  accepted := checks3290.2.2

def tau3291 : RatBall :=
  ⟨⟨-91/640, 237/640⟩, 3/1280⟩
def center3291 : GaussianRat :=
  ⟨-22680033/200000000, 131473549/500000000⟩
def contact3291 : RatBall := localContactBall tau3291 center3291
def work3291 : RoundedTauEval :=
  evalTau precision tau3291 contact3291 logTwoBall

theorem center_sq3291 : (center3291.re : ℝ)^2 +
    (center3291.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3291]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3291 : work3291.theta.ok = true ∧
    work3291.jac.invOK = true ∧ acceptsUnitSq work3291.out = true := by
  norm_num [work3291, contact3291, tau3291, center3291, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3291 : CellCertificate where
  tauBall := tau3291
  contactCenter := center3291
  contactBall := contact3291
  work := work3291
  center_sq := center_sq3291
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3291.1
  jac_ok := checks3291.2.1
  accepted := checks3291.2.2

def tau3292 : RatBall :=
  ⟨⟨-89/640, 237/640⟩, 3/1280⟩
def center3292 : GaussianRat :=
  ⟨-55484957/500000000, 65811399/250000000⟩
def contact3292 : RatBall := localContactBall tau3292 center3292
def work3292 : RoundedTauEval :=
  evalTau precision tau3292 contact3292 logTwoBall

theorem center_sq3292 : (center3292.re : ℝ)^2 +
    (center3292.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3292]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3292 : work3292.theta.ok = true ∧
    work3292.jac.invOK = true ∧ acceptsUnitSq work3292.out = true := by
  norm_num [work3292, contact3292, tau3292, center3292, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3292 : CellCertificate where
  tauBall := tau3292
  contactCenter := center3292
  contactBall := contact3292
  work := work3292
  center_sq := center_sq3292
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3292.1
  jac_ok := checks3292.2.1
  accepted := checks3292.2.2

def tau3293 : RatBall :=
  ⟨⟨-91/640, 239/640⟩, 3/1280⟩
def center3293 : GaussianRat :=
  ⟨-113703619/1000000000, 265378247/1000000000⟩
def contact3293 : RatBall := localContactBall tau3293 center3293
def work3293 : RoundedTauEval :=
  evalTau precision tau3293 contact3293 logTwoBall

theorem center_sq3293 : (center3293.re : ℝ)^2 +
    (center3293.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3293]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3293 : work3293.theta.ok = true ∧
    work3293.jac.invOK = true ∧ acceptsUnitSq work3293.out = true := by
  norm_num [work3293, contact3293, tau3293, center3293, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3293 : CellCertificate where
  tauBall := tau3293
  contactCenter := center3293
  contactBall := contact3293
  work := work3293
  center_sq := center_sq3293
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3293.1
  jac_ok := checks3293.2.1
  accepted := checks3293.2.2

def tau3294 : RatBall :=
  ⟨⟨-89/640, 239/640⟩, 3/1280⟩
def center3294 : GaussianRat :=
  ⟨-111267493/1000000000, 265680799/1000000000⟩
def contact3294 : RatBall := localContactBall tau3294 center3294
def work3294 : RoundedTauEval :=
  evalTau precision tau3294 contact3294 logTwoBall

theorem center_sq3294 : (center3294.re : ℝ)^2 +
    (center3294.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3294]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3294 : work3294.theta.ok = true ∧
    work3294.jac.invOK = true ∧ acceptsUnitSq work3294.out = true := by
  norm_num [work3294, contact3294, tau3294, center3294, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3294 : CellCertificate where
  tauBall := tau3294
  contactCenter := center3294
  contactBall := contact3294
  work := work3294
  center_sq := center_sq3294
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3294.1
  jac_ok := checks3294.2.1
  accepted := checks3294.2.2

def tau3295 : RatBall :=
  ⟨⟨-87/640, 233/640⟩, 3/1280⟩
def center3295 : GaussianRat :=
  ⟨-10796407/100000000, 129338763/500000000⟩
def contact3295 : RatBall := localContactBall tau3295 center3295
def work3295 : RoundedTauEval :=
  evalTau precision tau3295 contact3295 logTwoBall

theorem center_sq3295 : (center3295.re : ℝ)^2 +
    (center3295.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3295]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3295 : work3295.theta.ok = true ∧
    work3295.jac.invOK = true ∧ acceptsUnitSq work3295.out = true := by
  norm_num [work3295, contact3295, tau3295, center3295, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3295 : CellCertificate where
  tauBall := tau3295
  contactCenter := center3295
  contactBall := contact3295
  work := work3295
  center_sq := center_sq3295
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3295.1
  jac_ok := checks3295.2.1
  accepted := checks3295.2.2

def cells : List CellCertificate := [cell3288, cell3289, cell3290, cell3291, cell3292, cell3293, cell3294, cell3295]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411
