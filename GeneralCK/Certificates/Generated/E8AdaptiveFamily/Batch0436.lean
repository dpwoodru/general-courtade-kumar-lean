import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0436

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3488 : RatBall :=
  ⟨⟨-19/640, 253/640⟩, 3/1280⟩
def center3488 : GaussianRat :=
  ⟨-24541601/1000000000, 290103079/1000000000⟩
def contact3488 : RatBall := localContactBall tau3488 center3488
def work3488 : RoundedTauEval :=
  evalTau precision tau3488 contact3488 logTwoBall

theorem center_sq3488 : (center3488.re : ℝ)^2 +
    (center3488.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3488]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3488 : work3488.theta.ok = true ∧
    work3488.jac.invOK = true ∧ acceptsUnitSq work3488.out = true := by
  norm_num [work3488, contact3488, tau3488, center3488, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3488 : CellCertificate where
  tauBall := tau3488
  contactCenter := center3488
  contactBall := contact3488
  work := work3488
  center_sq := center_sq3488
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3488.1
  jac_ok := checks3488.2.1
  accepted := checks3488.2.2

def tau3489 : RatBall :=
  ⟨⟨-17/640, 253/640⟩, 3/1280⟩
def center3489 : GaussianRat :=
  ⟨-21961069/1000000000, 145086923/500000000⟩
def contact3489 : RatBall := localContactBall tau3489 center3489
def work3489 : RoundedTauEval :=
  evalTau precision tau3489 contact3489 logTwoBall

theorem center_sq3489 : (center3489.re : ℝ)^2 +
    (center3489.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3489]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3489 : work3489.theta.ok = true ∧
    work3489.jac.invOK = true ∧ acceptsUnitSq work3489.out = true := by
  norm_num [work3489, contact3489, tau3489, center3489, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3489 : CellCertificate where
  tauBall := tau3489
  contactCenter := center3489
  contactBall := contact3489
  work := work3489
  center_sq := center_sq3489
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3489.1
  jac_ok := checks3489.2.1
  accepted := checks3489.2.2

def tau3490 : RatBall :=
  ⟨⟨-19/640, 51/128⟩, 3/1280⟩
def center3490 : GaussianRat :=
  ⟨-24616799/1000000000, 73171759/250000000⟩
def contact3490 : RatBall := localContactBall tau3490 center3490
def work3490 : RoundedTauEval :=
  evalTau precision tau3490 contact3490 logTwoBall

theorem center_sq3490 : (center3490.re : ℝ)^2 +
    (center3490.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3490]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3490 : work3490.theta.ok = true ∧
    work3490.jac.invOK = true ∧ acceptsUnitSq work3490.out = true := by
  norm_num [work3490, contact3490, tau3490, center3490, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3490 : CellCertificate where
  tauBall := tau3490
  contactCenter := center3490
  contactBall := contact3490
  work := work3490
  center_sq := center_sq3490
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3490.1
  jac_ok := checks3490.2.1
  accepted := checks3490.2.2

def tau3491 : RatBall :=
  ⟨⟨-17/640, 51/128⟩, 3/1280⟩
def center3491 : GaussianRat :=
  ⟨-22028391/1000000000, 146379397/500000000⟩
def contact3491 : RatBall := localContactBall tau3491 center3491
def work3491 : RoundedTauEval :=
  evalTau precision tau3491 contact3491 logTwoBall

theorem center_sq3491 : (center3491.re : ℝ)^2 +
    (center3491.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3491]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3491 : work3491.theta.ok = true ∧
    work3491.jac.invOK = true ∧ acceptsUnitSq work3491.out = true := by
  norm_num [work3491, contact3491, tau3491, center3491, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3491 : CellCertificate where
  tauBall := tau3491
  contactCenter := center3491
  contactBall := contact3491
  work := work3491
  center_sq := center_sq3491
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3491.1
  jac_ok := checks3491.2.1
  accepted := checks3491.2.2

def tau3492 : RatBall :=
  ⟨⟨-3/128, 249/640⟩, 3/1280⟩
def center3492 : GaussianRat :=
  ⟨-19263193/1000000000, 142544269/500000000⟩
def contact3492 : RatBall := localContactBall tau3492 center3492
def work3492 : RoundedTauEval :=
  evalTau precision tau3492 contact3492 logTwoBall

theorem center_sq3492 : (center3492.re : ℝ)^2 +
    (center3492.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3492]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3492 : work3492.theta.ok = true ∧
    work3492.jac.invOK = true ∧ acceptsUnitSq work3492.out = true := by
  norm_num [work3492, contact3492, tau3492, center3492, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3492 : CellCertificate where
  tauBall := tau3492
  contactCenter := center3492
  contactBall := contact3492
  work := work3492
  center_sq := center_sq3492
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3492.1
  jac_ok := checks3492.2.1
  accepted := checks3492.2.2

def tau3493 : RatBall :=
  ⟨⟨-13/640, 249/640⟩, 3/1280⟩
def center3493 : GaussianRat :=
  ⟨-3339277/200000000, 71285531/250000000⟩
def contact3493 : RatBall := localContactBall tau3493 center3493
def work3493 : RoundedTauEval :=
  evalTau precision tau3493 contact3493 logTwoBall

theorem center_sq3493 : (center3493.re : ℝ)^2 +
    (center3493.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3493]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3493 : work3493.theta.ok = true ∧
    work3493.jac.invOK = true ∧ acceptsUnitSq work3493.out = true := by
  norm_num [work3493, contact3493, tau3493, center3493, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3493 : CellCertificate where
  tauBall := tau3493
  contactCenter := center3493
  contactBall := contact3493
  work := work3493
  center_sq := center_sq3493
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3493.1
  jac_ok := checks3493.2.1
  accepted := checks3493.2.2

def tau3494 : RatBall :=
  ⟨⟨-3/128, 251/640⟩, 3/1280⟩
def center3494 : GaussianRat :=
  ⟨-3864199/200000000, 57531759/200000000⟩
def contact3494 : RatBall := localContactBall tau3494 center3494
def work3494 : RoundedTauEval :=
  evalTau precision tau3494 contact3494 logTwoBall

theorem center_sq3494 : (center3494.re : ℝ)^2 +
    (center3494.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3494]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3494 : work3494.theta.ok = true ∧
    work3494.jac.invOK = true ∧ acceptsUnitSq work3494.out = true := by
  norm_num [work3494, contact3494, tau3494, center3494, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3494 : CellCertificate where
  tauBall := tau3494
  contactCenter := center3494
  contactBall := contact3494
  work := work3494
  center_sq := center_sq3494
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3494.1
  jac_ok := checks3494.2.1
  accepted := checks3494.2.2

def tau3495 : RatBall :=
  ⟨⟨-13/640, 251/640⟩, 3/1280⟩
def center3495 : GaussianRat :=
  ⟨-8373251/500000000, 287713133/1000000000⟩
def contact3495 : RatBall := localContactBall tau3495 center3495
def work3495 : RoundedTauEval :=
  evalTau precision tau3495 contact3495 logTwoBall

theorem center_sq3495 : (center3495.re : ℝ)^2 +
    (center3495.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3495]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3495 : work3495.theta.ok = true ∧
    work3495.jac.invOK = true ∧ acceptsUnitSq work3495.out = true := by
  norm_num [work3495, contact3495, tau3495, center3495, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3495 : CellCertificate where
  tauBall := tau3495
  contactCenter := center3495
  contactBall := contact3495
  work := work3495
  center_sq := center_sq3495
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3495.1
  jac_ok := checks3495.2.1
  accepted := checks3495.2.2

def cells : List CellCertificate := [cell3488, cell3489, cell3490, cell3491, cell3492, cell3493, cell3494, cell3495]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0436
