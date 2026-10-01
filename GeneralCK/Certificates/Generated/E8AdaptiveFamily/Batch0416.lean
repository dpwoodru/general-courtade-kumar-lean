import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3328 : RatBall :=
  ⟨⟨-87/640, 241/640⟩, 3/1280⟩
def center3328 : GaussianRat :=
  ⟨-109122947/1000000000, 53684517/200000000⟩
def contact3328 : RatBall := localContactBall tau3328 center3328
def work3328 : RoundedTauEval :=
  evalTau precision tau3328 contact3328 logTwoBall

theorem center_sq3328 : (center3328.re : ℝ)^2 +
    (center3328.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3328]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3328 : work3328.theta.ok = true ∧
    work3328.jac.invOK = true ∧ acceptsUnitSq work3328.out = true := by
  norm_num [work3328, contact3328, tau3328, center3328, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3328 : CellCertificate where
  tauBall := tau3328
  contactCenter := center3328
  contactBall := contact3328
  work := work3328
  center_sq := center_sq3328
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3328.1
  jac_ok := checks3328.2.1
  accepted := checks3328.2.2

def tau3329 : RatBall :=
  ⟨⟨-17/128, 241/640⟩, 3/1280⟩
def center3329 : GaussianRat :=
  ⟨-53336381/500000000, 268717167/1000000000⟩
def contact3329 : RatBall := localContactBall tau3329 center3329
def work3329 : RoundedTauEval :=
  evalTau precision tau3329 contact3329 logTwoBall

theorem center_sq3329 : (center3329.re : ℝ)^2 +
    (center3329.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3329]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3329 : work3329.theta.ok = true ∧
    work3329.jac.invOK = true ∧ acceptsUnitSq work3329.out = true := by
  norm_num [work3329, contact3329, tau3329, center3329, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3329 : CellCertificate where
  tauBall := tau3329
  contactCenter := center3329
  contactBall := contact3329
  work := work3329
  center_sq := center_sq3329
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3329.1
  jac_ok := checks3329.2.1
  accepted := checks3329.2.2

def tau3330 : RatBall :=
  ⟨⟨-83/640, 241/640⟩, 3/1280⟩
def center3330 : GaussianRat :=
  ⟨-104218637/1000000000, 134502819/500000000⟩
def contact3330 : RatBall := localContactBall tau3330 center3330
def work3330 : RoundedTauEval :=
  evalTau precision tau3330 contact3330 logTwoBall

theorem center_sq3330 : (center3330.re : ℝ)^2 +
    (center3330.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3330]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3330 : work3330.theta.ok = true ∧
    work3330.jac.invOK = true ∧ acceptsUnitSq work3330.out = true := by
  norm_num [work3330, contact3330, tau3330, center3330, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3330 : CellCertificate where
  tauBall := tau3330
  contactCenter := center3330
  contactBall := contact3330
  work := work3330
  center_sq := center_sq3330
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3330.1
  jac_ok := checks3330.2.1
  accepted := checks3330.2.2

def tau3331 : RatBall :=
  ⟨⟨-81/640, 241/640⟩, 3/1280⟩
def center3331 : GaussianRat :=
  ⟨-101760649/1000000000, 269287947/1000000000⟩
def contact3331 : RatBall := localContactBall tau3331 center3331
def work3331 : RoundedTauEval :=
  evalTau precision tau3331 contact3331 logTwoBall

theorem center_sq3331 : (center3331.re : ℝ)^2 +
    (center3331.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3331]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3331 : work3331.theta.ok = true ∧
    work3331.jac.invOK = true ∧ acceptsUnitSq work3331.out = true := by
  norm_num [work3331, contact3331, tau3331, center3331, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3331 : CellCertificate where
  tauBall := tau3331
  contactCenter := center3331
  contactBall := contact3331
  work := work3331
  center_sq := center_sq3331
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3331.1
  jac_ok := checks3331.2.1
  accepted := checks3331.2.2

def tau3332 : RatBall :=
  ⟨⟨-83/640, 243/640⟩, 3/1280⟩
def center3332 : GaussianRat :=
  ⟨-4180239/40000000, 271464801/1000000000⟩
def contact3332 : RatBall := localContactBall tau3332 center3332
def work3332 : RoundedTauEval :=
  evalTau precision tau3332 contact3332 logTwoBall

theorem center_sq3332 : (center3332.re : ℝ)^2 +
    (center3332.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3332]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3332 : work3332.theta.ok = true ∧
    work3332.jac.invOK = true ∧ acceptsUnitSq work3332.out = true := by
  norm_num [work3332, contact3332, tau3332, center3332, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3332 : CellCertificate where
  tauBall := tau3332
  contactCenter := center3332
  contactBall := contact3332
  work := work3332
  center_sq := center_sq3332
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3332.1
  jac_ok := checks3332.2.1
  accepted := checks3332.2.2

def tau3333 : RatBall :=
  ⟨⟨-81/640, 243/640⟩, 3/1280⟩
def center3333 : GaussianRat :=
  ⟨-51020881/500000000, 135875479/500000000⟩
def contact3333 : RatBall := localContactBall tau3333 center3333
def work3333 : RoundedTauEval :=
  evalTau precision tau3333 contact3333 logTwoBall

theorem center_sq3333 : (center3333.re : ℝ)^2 +
    (center3333.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3333]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3333 : work3333.theta.ok = true ∧
    work3333.jac.invOK = true ∧ acceptsUnitSq work3333.out = true := by
  norm_num [work3333, contact3333, tau3333, center3333, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3333 : CellCertificate where
  tauBall := tau3333
  contactCenter := center3333
  contactBall := contact3333
  work := work3333
  center_sq := center_sq3333
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3333.1
  jac_ok := checks3333.2.1
  accepted := checks3333.2.2

def tau3334 : RatBall :=
  ⟨⟨-79/640, 241/640⟩, 3/1280⟩
def center3334 : GaussianRat :=
  ⟨-99298877/1000000000, 134782023/500000000⟩
def contact3334 : RatBall := localContactBall tau3334 center3334
def work3334 : RoundedTauEval :=
  evalTau precision tau3334 contact3334 logTwoBall

theorem center_sq3334 : (center3334.re : ℝ)^2 +
    (center3334.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3334]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3334 : work3334.theta.ok = true ∧
    work3334.jac.invOK = true ∧ acceptsUnitSq work3334.out = true := by
  norm_num [work3334, contact3334, tau3334, center3334, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3334 : CellCertificate where
  tauBall := tau3334
  contactCenter := center3334
  contactBall := contact3334
  work := work3334
  center_sq := center_sq3334
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3334.1
  jac_ok := checks3334.2.1
  accepted := checks3334.2.2

def tau3335 : RatBall :=
  ⟨⟨-77/640, 241/640⟩, 3/1280⟩
def center3335 : GaussianRat :=
  ⟨-96833401/1000000000, 8432309/31250000⟩
def contact3335 : RatBall := localContactBall tau3335 center3335
def work3335 : RoundedTauEval :=
  evalTau precision tau3335 contact3335 logTwoBall

theorem center_sq3335 : (center3335.re : ℝ)^2 +
    (center3335.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3335]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3335 : work3335.theta.ok = true ∧
    work3335.jac.invOK = true ∧ acceptsUnitSq work3335.out = true := by
  norm_num [work3335, contact3335, tau3335, center3335, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3335 : CellCertificate where
  tauBall := tau3335
  contactCenter := center3335
  contactBall := contact3335
  work := work3335
  center_sq := center_sq3335
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3335.1
  jac_ok := checks3335.2.1
  accepted := checks3335.2.2

def cells : List CellCertificate := [cell3328, cell3329, cell3330, cell3331, cell3332, cell3333, cell3334, cell3335]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416
