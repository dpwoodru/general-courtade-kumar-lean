import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3344 : RatBall :=
  ⟨⟨-73/640, 49/128⟩, 3/1280⟩
def center3344 : GaussianRat :=
  ⟨-92406637/1000000000, 275316291/1000000000⟩
def contact3344 : RatBall := localContactBall tau3344 center3344
def work3344 : RoundedTauEval :=
  evalTau precision tau3344 contact3344 logTwoBall

theorem center_sq3344 : (center3344.re : ℝ)^2 +
    (center3344.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3344]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3344 : work3344.theta.ok = true ∧
    work3344.jac.invOK = true ∧ acceptsUnitSq work3344.out = true := by
  norm_num [work3344, contact3344, tau3344, center3344, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3344 : CellCertificate where
  tauBall := tau3344
  contactCenter := center3344
  contactBall := contact3344
  work := work3344
  center_sq := center_sq3344
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3344.1
  jac_ok := checks3344.2.1
  accepted := checks3344.2.2

def tau3345 : RatBall :=
  ⟨⟨-71/640, 241/640⟩, 3/1280⟩
def center3345 : GaussianRat :=
  ⟨-89415553/1000000000, 270605413/1000000000⟩
def contact3345 : RatBall := localContactBall tau3345 center3345
def work3345 : RoundedTauEval :=
  evalTau precision tau3345 contact3345 logTwoBall

theorem center_sq3345 : (center3345.re : ℝ)^2 +
    (center3345.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3345]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3345 : work3345.theta.ok = true ∧
    work3345.jac.invOK = true ∧ acceptsUnitSq work3345.out = true := by
  norm_num [work3345, contact3345, tau3345, center3345, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3345 : CellCertificate where
  tauBall := tau3345
  contactCenter := center3345
  contactBall := contact3345
  work := work3345
  center_sq := center_sq3345
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3345.1
  jac_ok := checks3345.2.1
  accepted := checks3345.2.2

def tau3346 : RatBall :=
  ⟨⟨-69/640, 241/640⟩, 3/1280⟩
def center3346 : GaussianRat :=
  ⟨-10867009/125000000, 67712443/250000000⟩
def contact3346 : RatBall := localContactBall tau3346 center3346
def work3346 : RoundedTauEval :=
  evalTau precision tau3346 contact3346 logTwoBall

theorem center_sq3346 : (center3346.re : ℝ)^2 +
    (center3346.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3346]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3346 : work3346.theta.ok = true ∧
    work3346.jac.invOK = true ∧ acceptsUnitSq work3346.out = true := by
  norm_num [work3346, contact3346, tau3346, center3346, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3346 : CellCertificate where
  tauBall := tau3346
  contactCenter := center3346
  contactBall := contact3346
  work := work3346
  center_sq := center_sq3346
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3346.1
  jac_ok := checks3346.2.1
  accepted := checks3346.2.2

def tau3347 : RatBall :=
  ⟨⟨-71/640, 243/640⟩, 3/1280⟩
def center3347 : GaussianRat :=
  ⟨-89664833/1000000000, 68271613/250000000⟩
def contact3347 : RatBall := localContactBall tau3347 center3347
def work3347 : RoundedTauEval :=
  evalTau precision tau3347 contact3347 logTwoBall

theorem center_sq3347 : (center3347.re : ℝ)^2 +
    (center3347.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3347 : work3347.theta.ok = true ∧
    work3347.jac.invOK = true ∧ acceptsUnitSq work3347.out = true := by
  norm_num [work3347, contact3347, tau3347, center3347, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3347 : CellCertificate where
  tauBall := tau3347
  contactCenter := center3347
  contactBall := contact3347
  work := work3347
  center_sq := center_sq3347
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3347.1
  jac_ok := checks3347.2.1
  accepted := checks3347.2.2

def tau3348 : RatBall :=
  ⟨⟨-69/640, 243/640⟩, 3/1280⟩
def center3348 : GaussianRat :=
  ⟨-87178851/1000000000, 273334167/1000000000⟩
def contact3348 : RatBall := localContactBall tau3348 center3348
def work3348 : RoundedTauEval :=
  evalTau precision tau3348 contact3348 logTwoBall

theorem center_sq3348 : (center3348.re : ℝ)^2 +
    (center3348.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3348]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3348 : work3348.theta.ok = true ∧
    work3348.jac.invOK = true ∧ acceptsUnitSq work3348.out = true := by
  norm_num [work3348, contact3348, tau3348, center3348, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3348 : CellCertificate where
  tauBall := tau3348
  contactCenter := center3348
  contactBall := contact3348
  work := work3348
  center_sq := center_sq3348
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3348.1
  jac_ok := checks3348.2.1
  accepted := checks3348.2.2

def tau3349 : RatBall :=
  ⟨⟨-67/640, 241/640⟩, 3/1280⟩
def center3349 : GaussianRat :=
  ⟨-84453299/1000000000, 5421753/20000000⟩
def contact3349 : RatBall := localContactBall tau3349 center3349
def work3349 : RoundedTauEval :=
  evalTau precision tau3349 contact3349 logTwoBall

theorem center_sq3349 : (center3349.re : ℝ)^2 +
    (center3349.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3349]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3349 : work3349.theta.ok = true ∧
    work3349.jac.invOK = true ∧ acceptsUnitSq work3349.out = true := by
  norm_num [work3349, contact3349, tau3349, center3349, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3349 : CellCertificate where
  tauBall := tau3349
  contactCenter := center3349
  contactBall := contact3349
  work := work3349
  center_sq := center_sq3349
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3349.1
  jac_ok := checks3349.2.1
  accepted := checks3349.2.2

def tau3350 : RatBall :=
  ⟨⟨-13/128, 241/640⟩, 3/1280⟩
def center3350 : GaussianRat :=
  ⟨-40983659/500000000, 135659503/500000000⟩
def contact3350 : RatBall := localContactBall tau3350 center3350
def work3350 : RoundedTauEval :=
  evalTau precision tau3350 contact3350 logTwoBall

theorem center_sq3350 : (center3350.re : ℝ)^2 +
    (center3350.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3350]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3350 : work3350.theta.ok = true ∧
    work3350.jac.invOK = true ∧ acceptsUnitSq work3350.out = true := by
  norm_num [work3350, contact3350, tau3350, center3350, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3350 : CellCertificate where
  tauBall := tau3350
  contactCenter := center3350
  contactBall := contact3350
  work := work3350
  center_sq := center_sq3350
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3350.1
  jac_ok := checks3350.2.1
  accepted := checks3350.2.2

def tau3351 : RatBall :=
  ⟨⟨-67/640, 243/640⟩, 3/1280⟩
def center3351 : GaussianRat :=
  ⟨-42344767/500000000, 273575317/1000000000⟩
def contact3351 : RatBall := localContactBall tau3351 center3351
def work3351 : RoundedTauEval :=
  evalTau precision tau3351 contact3351 logTwoBall

theorem center_sq3351 : (center3351.re : ℝ)^2 +
    (center3351.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3351]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3351 : work3351.theta.ok = true ∧
    work3351.jac.invOK = true ∧ acceptsUnitSq work3351.out = true := by
  norm_num [work3351, contact3351, tau3351, center3351, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3351 : CellCertificate where
  tauBall := tau3351
  contactCenter := center3351
  contactBall := contact3351
  work := work3351
  center_sq := center_sq3351
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3351.1
  jac_ok := checks3351.2.1
  accepted := checks3351.2.2

def cells : List CellCertificate := [cell3344, cell3345, cell3346, cell3347, cell3348, cell3349, cell3350, cell3351]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418
