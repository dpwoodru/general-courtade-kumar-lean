import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3560 : RatBall :=
  ⟨⟨5/128, 49/128⟩, 3/1280⟩
def center3560 : GaussianRat :=
  ⟨31895051/1000000000, 13979961/50000000⟩
def contact3560 : RatBall := localContactBall tau3560 center3560
def work3560 : RoundedTauEval :=
  evalTau precision tau3560 contact3560 logTwoBall

theorem center_sq3560 : (center3560.re : ℝ)^2 +
    (center3560.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3560]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3560 : work3560.theta.ok = true ∧
    work3560.jac.invOK = true ∧ acceptsUnitSq work3560.out = true := by
  norm_num [work3560, contact3560, tau3560, center3560, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3560 : CellCertificate where
  tauBall := tau3560
  contactCenter := center3560
  contactBall := contact3560
  work := work3560
  center_sq := center_sq3560
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3560.1
  jac_ok := checks3560.2.1
  accepted := checks3560.2.2

def tau3561 : RatBall :=
  ⟨⟨27/640, 49/128⟩, 3/1280⟩
def center3561 : GaussianRat :=
  ⟨1076269/31250000, 69875701/250000000⟩
def contact3561 : RatBall := localContactBall tau3561 center3561
def work3561 : RoundedTauEval :=
  evalTau precision tau3561 contact3561 logTwoBall

theorem center_sq3561 : (center3561.re : ℝ)^2 +
    (center3561.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3561]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3561 : work3561.theta.ok = true ∧
    work3561.jac.invOK = true ∧ acceptsUnitSq work3561.out = true := by
  norm_num [work3561, contact3561, tau3561, center3561, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3561 : CellCertificate where
  tauBall := tau3561
  contactCenter := center3561
  contactBall := contact3561
  work := work3561
  center_sq := center_sq3561
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3561.1
  jac_ok := checks3561.2.1
  accepted := checks3561.2.2

def tau3562 : RatBall :=
  ⟨⟨5/128, 247/640⟩, 3/1280⟩
def center3562 : GaussianRat :=
  ⟨7997111/250000000, 282149129/1000000000⟩
def contact3562 : RatBall := localContactBall tau3562 center3562
def work3562 : RoundedTauEval :=
  evalTau precision tau3562 contact3562 logTwoBall

theorem center_sq3562 : (center3562.re : ℝ)^2 +
    (center3562.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3562]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3562 : work3562.theta.ok = true ∧
    work3562.jac.invOK = true ∧ acceptsUnitSq work3562.out = true := by
  norm_num [work3562, contact3562, tau3562, center3562, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3562 : CellCertificate where
  tauBall := tau3562
  contactCenter := center3562
  contactBall := contact3562
  work := work3562
  center_sq := center_sq3562
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3562.1
  jac_ok := checks3562.2.1
  accepted := checks3562.2.2

def tau3563 : RatBall :=
  ⟨⟨27/640, 247/640⟩, 3/1280⟩
def center3563 : GaussianRat :=
  ⟨34541389/1000000000, 56410273/200000000⟩
def contact3563 : RatBall := localContactBall tau3563 center3563
def work3563 : RoundedTauEval :=
  evalTau precision tau3563 contact3563 logTwoBall

theorem center_sq3563 : (center3563.re : ℝ)^2 +
    (center3563.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3563]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3563 : work3563.theta.ok = true ∧
    work3563.jac.invOK = true ∧ acceptsUnitSq work3563.out = true := by
  norm_num [work3563, contact3563, tau3563, center3563, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3563 : CellCertificate where
  tauBall := tau3563
  contactCenter := center3563
  contactBall := contact3563
  work := work3563
  center_sq := center_sq3563
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3563.1
  jac_ok := checks3563.2.1
  accepted := checks3563.2.2

def tau3564 : RatBall :=
  ⟨⟨29/640, 49/128⟩, 3/1280⟩
def center3564 : GaussianRat :=
  ⟨4623097/125000000, 13969953/50000000⟩
def contact3564 : RatBall := localContactBall tau3564 center3564
def work3564 : RoundedTauEval :=
  evalTau precision tau3564 contact3564 logTwoBall

theorem center_sq3564 : (center3564.re : ℝ)^2 +
    (center3564.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3564]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3564 : work3564.theta.ok = true ∧
    work3564.jac.invOK = true ∧ acceptsUnitSq work3564.out = true := by
  norm_num [work3564, contact3564, tau3564, center3564, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3564 : CellCertificate where
  tauBall := tau3564
  contactCenter := center3564
  contactBall := contact3564
  work := work3564
  center_sq := center_sq3564
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3564.1
  jac_ok := checks3564.2.1
  accepted := checks3564.2.2

def tau3565 : RatBall :=
  ⟨⟨31/640, 49/128⟩, 3/1280⟩
def center3565 : GaussianRat :=
  ⟨19763727/500000000, 279288009/1000000000⟩
def contact3565 : RatBall := localContactBall tau3565 center3565
def work3565 : RoundedTauEval :=
  evalTau precision tau3565 contact3565 logTwoBall

theorem center_sq3565 : (center3565.re : ℝ)^2 +
    (center3565.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3565]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3565 : work3565.theta.ok = true ∧
    work3565.jac.invOK = true ∧ acceptsUnitSq work3565.out = true := by
  norm_num [work3565, contact3565, tau3565, center3565, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3565 : CellCertificate where
  tauBall := tau3565
  contactCenter := center3565
  contactBall := contact3565
  work := work3565
  center_sq := center_sq3565
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3565.1
  jac_ok := checks3565.2.1
  accepted := checks3565.2.2

def tau3566 : RatBall :=
  ⟨⟨29/640, 247/640⟩, 3/1280⟩
def center3566 : GaussianRat :=
  ⟨18546463/500000000, 281946171/1000000000⟩
def contact3566 : RatBall := localContactBall tau3566 center3566
def work3566 : RoundedTauEval :=
  evalTau precision tau3566 contact3566 logTwoBall

theorem center_sq3566 : (center3566.re : ℝ)^2 +
    (center3566.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3566]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3566 : work3566.theta.ok = true ∧
    work3566.jac.invOK = true ∧ acceptsUnitSq work3566.out = true := by
  norm_num [work3566, contact3566, tau3566, center3566, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3566 : CellCertificate where
  tauBall := tau3566
  contactCenter := center3566
  contactBall := contact3566
  work := work3566
  center_sq := center_sq3566
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3566.1
  jac_ok := checks3566.2.1
  accepted := checks3566.2.2

def tau3567 : RatBall :=
  ⟨⟨31/640, 247/640⟩, 3/1280⟩
def center3567 : GaussianRat :=
  ⟨4955369/125000000, 8807299/31250000⟩
def contact3567 : RatBall := localContactBall tau3567 center3567
def work3567 : RoundedTauEval :=
  evalTau precision tau3567 contact3567 logTwoBall

theorem center_sq3567 : (center3567.re : ℝ)^2 +
    (center3567.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3567]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3567 : work3567.theta.ok = true ∧
    work3567.jac.invOK = true ∧ acceptsUnitSq work3567.out = true := by
  norm_num [work3567, contact3567, tau3567, center3567, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3567 : CellCertificate where
  tauBall := tau3567
  contactCenter := center3567
  contactBall := contact3567
  work := work3567
  center_sq := center_sq3567
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3567.1
  jac_ok := checks3567.2.1
  accepted := checks3567.2.2

def cells : List CellCertificate := [cell3560, cell3561, cell3562, cell3563, cell3564, cell3565, cell3566, cell3567]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445
