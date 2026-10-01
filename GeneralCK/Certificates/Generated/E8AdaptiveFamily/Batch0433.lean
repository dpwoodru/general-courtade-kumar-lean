import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3464 : RatBall :=
  ⟨⟨-27/640, 249/640⟩, 3/1280⟩
def center3464 : GaussianRat :=
  ⟨-34643579/1000000000, 56921471/200000000⟩
def contact3464 : RatBall := localContactBall tau3464 center3464
def work3464 : RoundedTauEval :=
  evalTau precision tau3464 contact3464 logTwoBall

theorem center_sq3464 : (center3464.re : ℝ)^2 +
    (center3464.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3464]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3464 : work3464.theta.ok = true ∧
    work3464.jac.invOK = true ∧ acceptsUnitSq work3464.out = true := by
  norm_num [work3464, contact3464, tau3464, center3464, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3464 : CellCertificate where
  tauBall := tau3464
  contactCenter := center3464
  contactBall := contact3464
  work := work3464
  center_sq := center_sq3464
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3464.1
  jac_ok := checks3464.2.1
  accepted := checks3464.2.2

def tau3465 : RatBall :=
  ⟨⟨-5/128, 249/640⟩, 3/1280⟩
def center3465 : GaussianRat :=
  ⟨-32083143/1000000000, 142353243/500000000⟩
def contact3465 : RatBall := localContactBall tau3465 center3465
def work3465 : RoundedTauEval :=
  evalTau precision tau3465 contact3465 logTwoBall

theorem center_sq3465 : (center3465.re : ℝ)^2 +
    (center3465.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3465]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3465 : work3465.theta.ok = true ∧
    work3465.jac.invOK = true ∧ acceptsUnitSq work3465.out = true := by
  norm_num [work3465, contact3465, tau3465, center3465, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3465 : CellCertificate where
  tauBall := tau3465
  contactCenter := center3465
  contactBall := contact3465
  work := work3465
  center_sq := center_sq3465
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3465.1
  jac_ok := checks3465.2.1
  accepted := checks3465.2.2

def tau3466 : RatBall :=
  ⟨⟨-27/640, 251/640⟩, 3/1280⟩
def center3466 : GaussianRat :=
  ⟨-17373599/500000000, 287170877/1000000000⟩
def contact3466 : RatBall := localContactBall tau3466 center3466
def work3466 : RoundedTauEval :=
  evalTau precision tau3466 contact3466 logTwoBall

theorem center_sq3466 : (center3466.re : ℝ)^2 +
    (center3466.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3466]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3466 : work3466.theta.ok = true ∧
    work3466.jac.invOK = true ∧ acceptsUnitSq work3466.out = true := by
  norm_num [work3466, contact3466, tau3466, center3466, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3466 : CellCertificate where
  tauBall := tau3466
  contactCenter := center3466
  contactBall := contact3466
  work := work3466
  center_sq := center_sq3466
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3466.1
  jac_ok := checks3466.2.1
  accepted := checks3466.2.2

def tau3467 : RatBall :=
  ⟨⟨-5/128, 251/640⟩, 3/1280⟩
def center3467 : GaussianRat :=
  ⟨-32179167/1000000000, 57454279/200000000⟩
def contact3467 : RatBall := localContactBall tau3467 center3467
def work3467 : RoundedTauEval :=
  evalTau precision tau3467 contact3467 logTwoBall

theorem center_sq3467 : (center3467.re : ℝ)^2 +
    (center3467.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3467]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3467 : work3467.theta.ok = true ∧
    work3467.jac.invOK = true ∧ acceptsUnitSq work3467.out = true := by
  norm_num [work3467, contact3467, tau3467, center3467, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3467 : CellCertificate where
  tauBall := tau3467
  contactCenter := center3467
  contactBall := contact3467
  work := work3467
  center_sq := center_sq3467
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3467.1
  jac_ok := checks3467.2.1
  accepted := checks3467.2.2

def tau3468 : RatBall :=
  ⟨⟨-31/640, 253/640⟩, 3/1280⟩
def center3468 : GaussianRat :=
  ⟨-9999803/250000000, 36189373/125000000⟩
def contact3468 : RatBall := localContactBall tau3468 center3468
def work3468 : RoundedTauEval :=
  evalTau precision tau3468 contact3468 logTwoBall

theorem center_sq3468 : (center3468.re : ℝ)^2 +
    (center3468.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3468]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3468 : work3468.theta.ok = true ∧
    work3468.jac.invOK = true ∧ acceptsUnitSq work3468.out = true := by
  norm_num [work3468, contact3468, tau3468, center3468, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3468 : CellCertificate where
  tauBall := tau3468
  contactCenter := center3468
  contactBall := contact3468
  work := work3468
  center_sq := center_sq3468
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3468.1
  jac_ok := checks3468.2.1
  accepted := checks3468.2.2

def tau3469 : RatBall :=
  ⟨⟨-29/640, 253/640⟩, 3/1280⟩
def center3469 : GaussianRat :=
  ⟨-18713263/500000000, 289632371/1000000000⟩
def contact3469 : RatBall := localContactBall tau3469 center3469
def work3469 : RoundedTauEval :=
  evalTau precision tau3469 contact3469 logTwoBall

theorem center_sq3469 : (center3469.re : ℝ)^2 +
    (center3469.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3469]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3469 : work3469.theta.ok = true ∧
    work3469.jac.invOK = true ∧ acceptsUnitSq work3469.out = true := by
  norm_num [work3469, contact3469, tau3469, center3469, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3469 : CellCertificate where
  tauBall := tau3469
  contactCenter := center3469
  contactBall := contact3469
  work := work3469
  center_sq := center_sq3469
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3469.1
  jac_ok := checks3469.2.1
  accepted := checks3469.2.2

def tau3470 : RatBall :=
  ⟨⟨-31/640, 51/128⟩, 3/1280⟩
def center3470 : GaussianRat :=
  ⟨-20060649/500000000, 146045357/500000000⟩
def contact3470 : RatBall := localContactBall tau3470 center3470
def work3470 : RoundedTauEval :=
  evalTau precision tau3470 contact3470 logTwoBall

theorem center_sq3470 : (center3470.re : ℝ)^2 +
    (center3470.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3470]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3470 : work3470.theta.ok = true ∧
    work3470.jac.invOK = true ∧ acceptsUnitSq work3470.out = true := by
  norm_num [work3470, contact3470, tau3470, center3470, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3470 : CellCertificate where
  tauBall := tau3470
  contactCenter := center3470
  contactBall := contact3470
  work := work3470
  center_sq := center_sq3470
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3470.1
  jac_ok := checks3470.2.1
  accepted := checks3470.2.2

def tau3471 : RatBall :=
  ⟨⟨-29/640, 51/128⟩, 3/1280⟩
def center3471 : GaussianRat :=
  ⟨-2346303/62500000, 292209741/1000000000⟩
def contact3471 : RatBall := localContactBall tau3471 center3471
def work3471 : RoundedTauEval :=
  evalTau precision tau3471 contact3471 logTwoBall

theorem center_sq3471 : (center3471.re : ℝ)^2 +
    (center3471.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3471]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3471 : work3471.theta.ok = true ∧
    work3471.jac.invOK = true ∧ acceptsUnitSq work3471.out = true := by
  norm_num [work3471, contact3471, tau3471, center3471, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3471 : CellCertificate where
  tauBall := tau3471
  contactCenter := center3471
  contactBall := contact3471
  work := work3471
  center_sq := center_sq3471
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3471.1
  jac_ok := checks3471.2.1
  accepted := checks3471.2.2

def cells : List CellCertificate := [cell3464, cell3465, cell3466, cell3467, cell3468, cell3469, cell3470, cell3471]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433
