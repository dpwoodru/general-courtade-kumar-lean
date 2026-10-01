import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3392 : RatBall :=
  ⟨⟨-49/640, 247/640⟩, 3/1280⟩
def center3392 : GaussianRat :=
  ⟨-6250857/100000000, 280490707/1000000000⟩
def contact3392 : RatBall := localContactBall tau3392 center3392
def work3392 : RoundedTauEval :=
  evalTau precision tau3392 contact3392 logTwoBall

theorem center_sq3392 : (center3392.re : ℝ)^2 +
    (center3392.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3392]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3392 : work3392.theta.ok = true ∧
    work3392.jac.invOK = true ∧ acceptsUnitSq work3392.out = true := by
  norm_num [work3392, contact3392, tau3392, center3392, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3392 : CellCertificate where
  tauBall := tau3392
  contactCenter := center3392
  contactBall := contact3392
  work := work3392
  center_sq := center_sq3392
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3392.1
  jac_ok := checks3392.2.1
  accepted := checks3392.2.2

def tau3393 : RatBall :=
  ⟨⟨-63/640, 249/640⟩, 3/1280⟩
def center3393 : GaussianRat :=
  ⟨-16077783/200000000, 281560103/1000000000⟩
def contact3393 : RatBall := localContactBall tau3393 center3393
def work3393 : RoundedTauEval :=
  evalTau precision tau3393 contact3393 logTwoBall

theorem center_sq3393 : (center3393.re : ℝ)^2 +
    (center3393.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3393]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3393 : work3393.theta.ok = true ∧
    work3393.jac.invOK = true ∧ acceptsUnitSq work3393.out = true := by
  norm_num [work3393, contact3393, tau3393, center3393, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3393 : CellCertificate where
  tauBall := tau3393
  contactCenter := center3393
  contactBall := contact3393
  work := work3393
  center_sq := center_sq3393
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3393.1
  jac_ok := checks3393.2.1
  accepted := checks3393.2.2

def tau3394 : RatBall :=
  ⟨⟨-61/640, 249/640⟩, 3/1280⟩
def center3394 : GaussianRat :=
  ⟨-38934787/500000000, 281790577/1000000000⟩
def contact3394 : RatBall := localContactBall tau3394 center3394
def work3394 : RoundedTauEval :=
  evalTau precision tau3394 contact3394 logTwoBall

theorem center_sq3394 : (center3394.re : ℝ)^2 +
    (center3394.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3394]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3394 : work3394.theta.ok = true ∧
    work3394.jac.invOK = true ∧ acceptsUnitSq work3394.out = true := by
  norm_num [work3394, contact3394, tau3394, center3394, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3394 : CellCertificate where
  tauBall := tau3394
  contactCenter := center3394
  contactBall := contact3394
  work := work3394
  center_sq := center_sq3394
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3394.1
  jac_ok := checks3394.2.1
  accepted := checks3394.2.2

def tau3395 : RatBall :=
  ⟨⟨-59/640, 249/640⟩, 3/1280⟩
def center3395 : GaussianRat :=
  ⟨-75347127/1000000000, 8812939/31250000⟩
def contact3395 : RatBall := localContactBall tau3395 center3395
def work3395 : RoundedTauEval :=
  evalTau precision tau3395 contact3395 logTwoBall

theorem center_sq3395 : (center3395.re : ℝ)^2 +
    (center3395.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3395]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3395 : work3395.theta.ok = true ∧
    work3395.jac.invOK = true ∧ acceptsUnitSq work3395.out = true := by
  norm_num [work3395, contact3395, tau3395, center3395, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3395 : CellCertificate where
  tauBall := tau3395
  contactCenter := center3395
  contactBall := contact3395
  work := work3395
  center_sq := center_sq3395
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3395.1
  jac_ok := checks3395.2.1
  accepted := checks3395.2.2

def tau3396 : RatBall :=
  ⟨⟨-57/640, 249/640⟩, 3/1280⟩
def center3396 : GaussianRat :=
  ⟨-14564333/200000000, 70557619/250000000⟩
def contact3396 : RatBall := localContactBall tau3396 center3396
def work3396 : RoundedTauEval :=
  evalTau precision tau3396 contact3396 logTwoBall

theorem center_sq3396 : (center3396.re : ℝ)^2 +
    (center3396.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3396]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3396 : work3396.theta.ok = true ∧
    work3396.jac.invOK = true ∧ acceptsUnitSq work3396.out = true := by
  norm_num [work3396, contact3396, tau3396, center3396, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3396 : CellCertificate where
  tauBall := tau3396
  contactCenter := center3396
  contactBall := contact3396
  work := work3396
  center_sq := center_sq3396
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3396.1
  jac_ok := checks3396.2.1
  accepted := checks3396.2.2

def tau3397 : RatBall :=
  ⟨⟨-11/128, 249/640⟩, 3/1280⟩
def center3397 : GaussianRat :=
  ⟨-70293283/1000000000, 14121991/50000000⟩
def contact3397 : RatBall := localContactBall tau3397 center3397
def work3397 : RoundedTauEval :=
  evalTau precision tau3397 contact3397 logTwoBall

theorem center_sq3397 : (center3397.re : ℝ)^2 +
    (center3397.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3397]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3397 : work3397.theta.ok = true ∧
    work3397.jac.invOK = true ∧ acceptsUnitSq work3397.out = true := by
  norm_num [work3397, contact3397, tau3397, center3397, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3397 : CellCertificate where
  tauBall := tau3397
  contactCenter := center3397
  contactBall := contact3397
  work := work3397
  center_sq := center_sq3397
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3397.1
  jac_ok := checks3397.2.1
  accepted := checks3397.2.2

def tau3398 : RatBall :=
  ⟨⟨-53/640, 249/640⟩, 3/1280⟩
def center3398 : GaussianRat :=
  ⟨-33881037/500000000, 282642041/1000000000⟩
def contact3398 : RatBall := localContactBall tau3398 center3398
def work3398 : RoundedTauEval :=
  evalTau precision tau3398 contact3398 logTwoBall

theorem center_sq3398 : (center3398.re : ℝ)^2 +
    (center3398.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3398]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3398 : work3398.theta.ok = true ∧
    work3398.jac.invOK = true ∧ acceptsUnitSq work3398.out = true := by
  norm_num [work3398, contact3398, tau3398, center3398, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3398 : CellCertificate where
  tauBall := tau3398
  contactCenter := center3398
  contactBall := contact3398
  work := work3398
  center_sq := center_sq3398
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3398.1
  jac_ok := checks3398.2.1
  accepted := checks3398.2.2

def tau3399 : RatBall :=
  ⟨⟨-11/128, 251/640⟩, 3/1280⟩
def center3399 : GaussianRat :=
  ⟨-70500491/1000000000, 35621651/125000000⟩
def contact3399 : RatBall := localContactBall tau3399 center3399
def work3399 : RoundedTauEval :=
  evalTau precision tau3399 contact3399 logTwoBall

theorem center_sq3399 : (center3399.re : ℝ)^2 +
    (center3399.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3399]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3399 : work3399.theta.ok = true ∧
    work3399.jac.invOK = true ∧ acceptsUnitSq work3399.out = true := by
  norm_num [work3399, contact3399, tau3399, center3399, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3399 : CellCertificate where
  tauBall := tau3399
  contactCenter := center3399
  contactBall := contact3399
  work := work3399
  center_sq := center_sq3399
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3399.1
  jac_ok := checks3399.2.1
  accepted := checks3399.2.2

def cells : List CellCertificate := [cell3392, cell3393, cell3394, cell3395, cell3396, cell3397, cell3398, cell3399]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424
