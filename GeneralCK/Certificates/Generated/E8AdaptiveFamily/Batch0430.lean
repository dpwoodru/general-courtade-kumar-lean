import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3440 : RatBall :=
  ⟨⟨-7/128, 249/640⟩, 3/1280⟩
def center3440 : GaussianRat :=
  ⟨-22435003/500000000, 284135717/1000000000⟩
def contact3440 : RatBall := localContactBall tau3440 center3440
def work3440 : RoundedTauEval :=
  evalTau precision tau3440 contact3440 logTwoBall

theorem center_sq3440 : (center3440.re : ℝ)^2 +
    (center3440.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3440]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3440 : work3440.theta.ok = true ∧
    work3440.jac.invOK = true ∧ acceptsUnitSq work3440.out = true := by
  norm_num [work3440, contact3440, tau3440, center3440, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3440 : CellCertificate where
  tauBall := tau3440
  contactCenter := center3440
  contactBall := contact3440
  work := work3440
  center_sq := center_sq3440
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3440.1
  jac_ok := checks3440.2.1
  accepted := checks3440.2.2

def tau3441 : RatBall :=
  ⟨⟨-33/640, 249/640⟩, 3/1280⟩
def center3441 : GaussianRat :=
  ⟨-42315903/1000000000, 284264849/1000000000⟩
def contact3441 : RatBall := localContactBall tau3441 center3441
def work3441 : RoundedTauEval :=
  evalTau precision tau3441 contact3441 logTwoBall

theorem center_sq3441 : (center3441.re : ℝ)^2 +
    (center3441.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3441]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3441 : work3441.theta.ok = true ∧
    work3441.jac.invOK = true ∧ acceptsUnitSq work3441.out = true := by
  norm_num [work3441, contact3441, tau3441, center3441, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3441 : CellCertificate where
  tauBall := tau3441
  contactCenter := center3441
  contactBall := contact3441
  work := work3441
  center_sq := center_sq3441
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3441.1
  jac_ok := checks3441.2.1
  accepted := checks3441.2.2

def tau3442 : RatBall :=
  ⟨⟨-7/128, 251/640⟩, 3/1280⟩
def center3442 : GaussianRat :=
  ⟨-45003787/1000000000, 57338531/200000000⟩
def contact3442 : RatBall := localContactBall tau3442 center3442
def work3442 : RoundedTauEval :=
  evalTau precision tau3442 contact3442 logTwoBall

theorem center_sq3442 : (center3442.re : ℝ)^2 +
    (center3442.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3442]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3442 : work3442.theta.ok = true ∧
    work3442.jac.invOK = true ∧ acceptsUnitSq work3442.out = true := by
  norm_num [work3442, contact3442, tau3442, center3442, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3442 : CellCertificate where
  tauBall := tau3442
  contactCenter := center3442
  contactBall := contact3442
  work := work3442
  center_sq := center_sq3442
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3442.1
  jac_ok := checks3442.2.1
  accepted := checks3442.2.2

def tau3443 : RatBall :=
  ⟨⟨-33/640, 251/640⟩, 3/1280⟩
def center3443 : GaussianRat :=
  ⟨-42442179/1000000000, 286823589/1000000000⟩
def contact3443 : RatBall := localContactBall tau3443 center3443
def work3443 : RoundedTauEval :=
  evalTau precision tau3443 contact3443 logTwoBall

theorem center_sq3443 : (center3443.re : ℝ)^2 +
    (center3443.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3443]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3443 : work3443.theta.ok = true ∧
    work3443.jac.invOK = true ∧ acceptsUnitSq work3443.out = true := by
  norm_num [work3443, contact3443, tau3443, center3443, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3443 : CellCertificate where
  tauBall := tau3443
  contactCenter := center3443
  contactBall := contact3443
  work := work3443
  center_sq := center_sq3443
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3443.1
  jac_ok := checks3443.2.1
  accepted := checks3443.2.2

def tau3444 : RatBall :=
  ⟨⟨-39/640, 253/640⟩, 3/1280⟩
def center3444 : GaussianRat :=
  ⟨-50272091/1000000000, 144484349/500000000⟩
def contact3444 : RatBall := localContactBall tau3444 center3444
def work3444 : RoundedTauEval :=
  evalTau precision tau3444 contact3444 logTwoBall

theorem center_sq3444 : (center3444.re : ℝ)^2 +
    (center3444.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3444]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3444 : work3444.theta.ok = true ∧
    work3444.jac.invOK = true ∧ acceptsUnitSq work3444.out = true := by
  norm_num [work3444, contact3444, tau3444, center3444, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3444 : CellCertificate where
  tauBall := tau3444
  contactCenter := center3444
  contactBall := contact3444
  work := work3444
  center_sq := center_sq3444
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3444.1
  jac_ok := checks3444.2.1
  accepted := checks3444.2.2

def tau3445 : RatBall :=
  ⟨⟨-37/640, 253/640⟩, 3/1280⟩
def center3445 : GaussianRat :=
  ⟨-47706761/1000000000, 36139591/125000000⟩
def contact3445 : RatBall := localContactBall tau3445 center3445
def work3445 : RoundedTauEval :=
  evalTau precision tau3445 contact3445 logTwoBall

theorem center_sq3445 : (center3445.re : ℝ)^2 +
    (center3445.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3445]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3445 : work3445.theta.ok = true ∧
    work3445.jac.invOK = true ∧ acceptsUnitSq work3445.out = true := by
  norm_num [work3445, contact3445, tau3445, center3445, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3445 : CellCertificate where
  tauBall := tau3445
  contactCenter := center3445
  contactBall := contact3445
  work := work3445
  center_sq := center_sq3445
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3445.1
  jac_ok := checks3445.2.1
  accepted := checks3445.2.2

def tau3446 : RatBall :=
  ⟨⟨-7/128, 253/640⟩, 3/1280⟩
def center3446 : GaussianRat :=
  ⟨-9027887/200000000, 289257137/1000000000⟩
def contact3446 : RatBall := localContactBall tau3446 center3446
def work3446 : RoundedTauEval :=
  evalTau precision tau3446 contact3446 logTwoBall

theorem center_sq3446 : (center3446.re : ℝ)^2 +
    (center3446.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3446]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3446 : work3446.theta.ok = true ∧
    work3446.jac.invOK = true ∧ acceptsUnitSq work3446.out = true := by
  norm_num [work3446, contact3446, tau3446, center3446, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3446 : CellCertificate where
  tauBall := tau3446
  contactCenter := center3446
  contactBall := contact3446
  work := work3446
  center_sq := center_sq3446
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3446.1
  jac_ok := checks3446.2.1
  accepted := checks3446.2.2

def tau3447 : RatBall :=
  ⟨⟨-33/640, 253/640⟩, 3/1280⟩
def center3447 : GaussianRat :=
  ⟨-42570217/1000000000, 144694949/500000000⟩
def contact3447 : RatBall := localContactBall tau3447 center3447
def work3447 : RoundedTauEval :=
  evalTau precision tau3447 contact3447 logTwoBall

theorem center_sq3447 : (center3447.re : ℝ)^2 +
    (center3447.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3447]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3447 : work3447.theta.ok = true ∧
    work3447.jac.invOK = true ∧ acceptsUnitSq work3447.out = true := by
  norm_num [work3447, contact3447, tau3447, center3447, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3447 : CellCertificate where
  tauBall := tau3447
  contactCenter := center3447
  contactBall := contact3447
  work := work3447
  center_sq := center_sq3447
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3447.1
  jac_ok := checks3447.2.1
  accepted := checks3447.2.2

def cells : List CellCertificate := [cell3440, cell3441, cell3442, cell3443, cell3444, cell3445, cell3446, cell3447]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430
