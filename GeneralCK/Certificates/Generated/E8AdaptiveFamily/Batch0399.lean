import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3192 : RatBall :=
  ⟨⟨131/640, -219/640⟩, 3/1280⟩
def center3192 : GaussianRat :=
  ⟨157607013/1000000000, -23500697/100000000⟩
def contact3192 : RatBall := localContactBall tau3192 center3192
def work3192 : RoundedTauEval :=
  evalTau precision tau3192 contact3192 logTwoBall

theorem center_sq3192 : (center3192.re : ℝ)^2 +
    (center3192.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3192 : work3192.theta.ok = true ∧
    work3192.jac.invOK = true ∧ acceptsUnitSq work3192.out = true := by
  norm_num [work3192, contact3192, tau3192, center3192, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3192 : CellCertificate where
  tauBall := tau3192
  contactCenter := center3192
  contactBall := contact3192
  work := work3192
  center_sq := center_sq3192
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3192.1
  jac_ok := checks3192.2.1
  accepted := checks3192.2.2

def tau3193 : RatBall :=
  ⟨⟨129/640, -217/640⟩, 3/1280⟩
def center3193 : GaussianRat :=
  ⟨38739093/250000000, -233070213/1000000000⟩
def contact3193 : RatBall := localContactBall tau3193 center3193
def work3193 : RoundedTauEval :=
  evalTau precision tau3193 contact3193 logTwoBall

theorem center_sq3193 : (center3193.re : ℝ)^2 +
    (center3193.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3193]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3193 : work3193.theta.ok = true ∧
    work3193.jac.invOK = true ∧ acceptsUnitSq work3193.out = true := by
  norm_num [work3193, contact3193, tau3193, center3193, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3193 : CellCertificate where
  tauBall := tau3193
  contactCenter := center3193
  contactBall := contact3193
  work := work3193
  center_sq := center_sq3193
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3193.1
  jac_ok := checks3193.2.1
  accepted := checks3193.2.2

def tau3194 : RatBall :=
  ⟨⟨131/640, -217/640⟩, 3/1280⟩
def center3194 : GaussianRat :=
  ⟨157247951/1000000000, -46543131/200000000⟩
def contact3194 : RatBall := localContactBall tau3194 center3194
def work3194 : RoundedTauEval :=
  evalTau precision tau3194 contact3194 logTwoBall

theorem center_sq3194 : (center3194.re : ℝ)^2 +
    (center3194.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3194 : work3194.theta.ok = true ∧
    work3194.jac.invOK = true ∧ acceptsUnitSq work3194.out = true := by
  norm_num [work3194, contact3194, tau3194, center3194, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3194 : CellCertificate where
  tauBall := tau3194
  contactCenter := center3194
  contactBall := contact3194
  work := work3194
  center_sq := center_sq3194
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3194.1
  jac_ok := checks3194.2.1
  accepted := checks3194.2.2

def tau3195 : RatBall :=
  ⟨⟨133/640, -219/640⟩, 3/1280⟩
def center3195 : GaussianRat :=
  ⟨159898033/1000000000, -234643387/1000000000⟩
def contact3195 : RatBall := localContactBall tau3195 center3195
def work3195 : RoundedTauEval :=
  evalTau precision tau3195 contact3195 logTwoBall

theorem center_sq3195 : (center3195.re : ℝ)^2 +
    (center3195.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3195]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3195 : work3195.theta.ok = true ∧
    work3195.jac.invOK = true ∧ acceptsUnitSq work3195.out = true := by
  norm_num [work3195, contact3195, tau3195, center3195, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3195 : CellCertificate where
  tauBall := tau3195
  contactCenter := center3195
  contactBall := contact3195
  work := work3195
  center_sq := center_sq3195
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3195.1
  jac_ok := checks3195.2.1
  accepted := checks3195.2.2

def tau3196 : RatBall :=
  ⟨⟨27/128, -219/640⟩, 3/1280⟩
def center3196 : GaussianRat :=
  ⟨162184187/1000000000, -234275597/1000000000⟩
def contact3196 : RatBall := localContactBall tau3196 center3196
def work3196 : RoundedTauEval :=
  evalTau precision tau3196 contact3196 logTwoBall

theorem center_sq3196 : (center3196.re : ℝ)^2 +
    (center3196.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3196]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3196 : work3196.theta.ok = true ∧
    work3196.jac.invOK = true ∧ acceptsUnitSq work3196.out = true := by
  norm_num [work3196, contact3196, tau3196, center3196, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3196 : CellCertificate where
  tauBall := tau3196
  contactCenter := center3196
  contactBall := contact3196
  work := work3196
  center_sq := center_sq3196
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3196.1
  jac_ok := checks3196.2.1
  accepted := checks3196.2.2

def tau3197 : RatBall :=
  ⟨⟨133/640, -217/640⟩, 3/1280⟩
def center3197 : GaussianRat :=
  ⟨79767381/500000000, -29044611/125000000⟩
def contact3197 : RatBall := localContactBall tau3197 center3197
def work3197 : RoundedTauEval :=
  evalTau precision tau3197 contact3197 logTwoBall

theorem center_sq3197 : (center3197.re : ℝ)^2 +
    (center3197.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3197]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3197 : work3197.theta.ok = true ∧
    work3197.jac.invOK = true ∧ acceptsUnitSq work3197.out = true := by
  norm_num [work3197, contact3197, tau3197, center3197, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3197 : CellCertificate where
  tauBall := tau3197
  contactCenter := center3197
  contactBall := contact3197
  work := work3197
  center_sq := center_sq3197
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3197.1
  jac_ok := checks3197.2.1
  accepted := checks3197.2.2

def tau3198 : RatBall :=
  ⟨⟨27/128, -217/640⟩, 3/1280⟩
def center3198 : GaussianRat :=
  ⟨80908379/500000000, -115996981/500000000⟩
def contact3198 : RatBall := localContactBall tau3198 center3198
def work3198 : RoundedTauEval :=
  evalTau precision tau3198 contact3198 logTwoBall

theorem center_sq3198 : (center3198.re : ℝ)^2 +
    (center3198.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3198]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3198 : work3198.theta.ok = true ∧
    work3198.jac.invOK = true ∧ acceptsUnitSq work3198.out = true := by
  norm_num [work3198, contact3198, tau3198, center3198, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3198 : CellCertificate where
  tauBall := tau3198
  contactCenter := center3198
  contactBall := contact3198
  work := work3198
  center_sq := center_sq3198
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3198.1
  jac_ok := checks3198.2.1
  accepted := checks3198.2.2

def tau3199 : RatBall :=
  ⟨⟨137/640, -217/640⟩, 3/1280⟩
def center3199 : GaussianRat :=
  ⟨41023473/250000000, -231626927/1000000000⟩
def contact3199 : RatBall := localContactBall tau3199 center3199
def work3199 : RoundedTauEval :=
  evalTau precision tau3199 contact3199 logTwoBall

theorem center_sq3199 : (center3199.re : ℝ)^2 +
    (center3199.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3199]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3199 : work3199.theta.ok = true ∧
    work3199.jac.invOK = true ∧ acceptsUnitSq work3199.out = true := by
  norm_num [work3199, contact3199, tau3199, center3199, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3199 : CellCertificate where
  tauBall := tau3199
  contactCenter := center3199
  contactBall := contact3199
  work := work3199
  center_sq := center_sq3199
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3199.1
  jac_ok := checks3199.2.1
  accepted := checks3199.2.2

def cells : List CellCertificate := [cell3192, cell3193, cell3194, cell3195, cell3196, cell3197, cell3198, cell3199]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399
