import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3336 : RatBall :=
  ⟨⟨-79/640, 243/640⟩, 3/1280⟩
def center3336 : GaussianRat :=
  ⟨-24893429/250000000, 136015413/500000000⟩
def contact3336 : RatBall := localContactBall tau3336 center3336
def work3336 : RoundedTauEval :=
  evalTau precision tau3336 contact3336 logTwoBall

theorem center_sq3336 : (center3336.re : ℝ)^2 +
    (center3336.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3336]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3336 : work3336.theta.ok = true ∧
    work3336.jac.invOK = true ∧ acceptsUnitSq work3336.out = true := by
  norm_num [work3336, contact3336, tau3336, center3336, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3336 : CellCertificate where
  tauBall := tau3336
  contactCenter := center3336
  contactBall := contact3336
  work := work3336
  center_sq := center_sq3336
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3336.1
  jac_ok := checks3336.2.1
  accepted := checks3336.2.2

def tau3337 : RatBall :=
  ⟨⟨-77/640, 243/640⟩, 3/1280⟩
def center3337 : GaussianRat :=
  ⟨-97101919/1000000000, 68076089/250000000⟩
def contact3337 : RatBall := localContactBall tau3337 center3337
def work3337 : RoundedTauEval :=
  evalTau precision tau3337 contact3337 logTwoBall

theorem center_sq3337 : (center3337.re : ℝ)^2 +
    (center3337.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3337]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3337 : work3337.theta.ok = true ∧
    work3337.jac.invOK = true ∧ acceptsUnitSq work3337.out = true := by
  norm_num [work3337, contact3337, tau3337, center3337, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3337 : CellCertificate where
  tauBall := tau3337
  contactCenter := center3337
  contactBall := contact3337
  work := work3337
  center_sq := center_sq3337
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3337.1
  jac_ok := checks3337.2.1
  accepted := checks3337.2.2

def tau3338 : RatBall :=
  ⟨⟨-15/128, 241/640⟩, 3/1280⟩
def center3338 : GaussianRat :=
  ⟨-943643/10000000, 270097427/1000000000⟩
def contact3338 : RatBall := localContactBall tau3338 center3338
def work3338 : RoundedTauEval :=
  evalTau precision tau3338 contact3338 logTwoBall

theorem center_sq3338 : (center3338.re : ℝ)^2 +
    (center3338.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3338]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3338 : work3338.theta.ok = true ∧
    work3338.jac.invOK = true ∧ acceptsUnitSq work3338.out = true := by
  norm_num [work3338, contact3338, tau3338, center3338, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3338 : CellCertificate where
  tauBall := tau3338
  contactCenter := center3338
  contactBall := contact3338
  work := work3338
  center_sq := center_sq3338
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3338.1
  jac_ok := checks3338.2.1
  accepted := checks3338.2.2

def tau3339 : RatBall :=
  ⟨⟨-73/640, 241/640⟩, 3/1280⟩
def center3339 : GaussianRat :=
  ⟨-11486457/125000000, 270354617/1000000000⟩
def contact3339 : RatBall := localContactBall tau3339 center3339
def work3339 : RoundedTauEval :=
  evalTau precision tau3339 contact3339 logTwoBall

theorem center_sq3339 : (center3339.re : ℝ)^2 +
    (center3339.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3339]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3339 : work3339.theta.ok = true ∧
    work3339.jac.invOK = true ∧ acceptsUnitSq work3339.out = true := by
  norm_num [work3339, contact3339, tau3339, center3339, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3339 : CellCertificate where
  tauBall := tau3339
  contactCenter := center3339
  contactBall := contact3339
  work := work3339
  center_sq := center_sq3339
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3339.1
  jac_ok := checks3339.2.1
  accepted := checks3339.2.2

def tau3340 : RatBall :=
  ⟨⟨-15/128, 243/640⟩, 3/1280⟩
def center3340 : GaussianRat :=
  ⟨-94626451/1000000000, 272571501/1000000000⟩
def contact3340 : RatBall := localContactBall tau3340 center3340
def work3340 : RoundedTauEval :=
  evalTau precision tau3340 contact3340 logTwoBall

theorem center_sq3340 : (center3340.re : ℝ)^2 +
    (center3340.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3340]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3340 : work3340.theta.ok = true ∧
    work3340.jac.invOK = true ∧ acceptsUnitSq work3340.out = true := by
  norm_num [work3340, contact3340, tau3340, center3340, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3340 : CellCertificate where
  tauBall := tau3340
  contactCenter := center3340
  contactBall := contact3340
  work := work3340
  center_sq := center_sq3340
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3340.1
  jac_ok := checks3340.2.1
  accepted := checks3340.2.2

def tau3341 : RatBall :=
  ⟨⟨-73/640, 243/640⟩, 3/1280⟩
def center3341 : GaussianRat :=
  ⟨-46073697/500000000, 54566443/200000000⟩
def contact3341 : RatBall := localContactBall tau3341 center3341
def work3341 : RoundedTauEval :=
  evalTau precision tau3341 contact3341 logTwoBall

theorem center_sq3341 : (center3341.re : ℝ)^2 +
    (center3341.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3341]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3341 : work3341.theta.ok = true ∧
    work3341.jac.invOK = true ∧ acceptsUnitSq work3341.out = true := by
  norm_num [work3341, contact3341, tau3341, center3341, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3341 : CellCertificate where
  tauBall := tau3341
  contactCenter := center3341
  contactBall := contact3341
  work := work3341
  center_sq := center_sq3341
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3341.1
  jac_ok := checks3341.2.1
  accepted := checks3341.2.2

def tau3342 : RatBall :=
  ⟨⟨-77/640, 49/128⟩, 3/1280⟩
def center3342 : GaussianRat :=
  ⟨-24343527/250000000, 34347651/125000000⟩
def contact3342 : RatBall := localContactBall tau3342 center3342
def work3342 : RoundedTauEval :=
  evalTau precision tau3342 contact3342 logTwoBall

theorem center_sq3342 : (center3342.re : ℝ)^2 +
    (center3342.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3342]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3342 : work3342.theta.ok = true ∧
    work3342.jac.invOK = true ∧ acceptsUnitSq work3342.out = true := by
  norm_num [work3342, contact3342, tau3342, center3342, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3342 : CellCertificate where
  tauBall := tau3342
  contactCenter := center3342
  contactBall := contact3342
  work := work3342
  center_sq := center_sq3342
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3342.1
  jac_ok := checks3342.2.1
  accepted := checks3342.2.2

def tau3343 : RatBall :=
  ⟨⟨-15/128, 49/128⟩, 3/1280⟩
def center3343 : GaussianRat :=
  ⟨-9489219/100000000, 275052007/1000000000⟩
def contact3343 : RatBall := localContactBall tau3343 center3343
def work3343 : RoundedTauEval :=
  evalTau precision tau3343 contact3343 logTwoBall

theorem center_sq3343 : (center3343.re : ℝ)^2 +
    (center3343.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3343]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3343 : work3343.theta.ok = true ∧
    work3343.jac.invOK = true ∧ acceptsUnitSq work3343.out = true := by
  norm_num [work3343, contact3343, tau3343, center3343, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3343 : CellCertificate where
  tauBall := tau3343
  contactCenter := center3343
  contactBall := contact3343
  work := work3343
  center_sq := center_sq3343
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3343.1
  jac_ok := checks3343.2.1
  accepted := checks3343.2.2

def cells : List CellCertificate := [cell3336, cell3337, cell3338, cell3339, cell3340, cell3341, cell3342, cell3343]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417
