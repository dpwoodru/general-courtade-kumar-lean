import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3448 : RatBall :=
  ⟨⟨-31/640, 49/128⟩, 3/1280⟩
def center3448 : GaussianRat :=
  ⟨-19763727/500000000, 279288009/1000000000⟩
def contact3448 : RatBall := localContactBall tau3448 center3448
def work3448 : RoundedTauEval :=
  evalTau precision tau3448 contact3448 logTwoBall

theorem center_sq3448 : (center3448.re : ℝ)^2 +
    (center3448.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3448]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3448 : work3448.theta.ok = true ∧
    work3448.jac.invOK = true ∧ acceptsUnitSq work3448.out = true := by
  norm_num [work3448, contact3448, tau3448, center3448, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3448 : CellCertificate where
  tauBall := tau3448
  contactCenter := center3448
  contactBall := contact3448
  work := work3448
  center_sq := center_sq3448
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3448.1
  jac_ok := checks3448.2.1
  accepted := checks3448.2.2

def tau3449 : RatBall :=
  ⟨⟨-29/640, 49/128⟩, 3/1280⟩
def center3449 : GaussianRat :=
  ⟨-4623097/125000000, 13969953/50000000⟩
def contact3449 : RatBall := localContactBall tau3449 center3449
def work3449 : RoundedTauEval :=
  evalTau precision tau3449 contact3449 logTwoBall

theorem center_sq3449 : (center3449.re : ℝ)^2 +
    (center3449.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3449]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3449 : work3449.theta.ok = true ∧
    work3449.jac.invOK = true ∧ acceptsUnitSq work3449.out = true := by
  norm_num [work3449, contact3449, tau3449, center3449, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3449 : CellCertificate where
  tauBall := tau3449
  contactCenter := center3449
  contactBall := contact3449
  work := work3449
  center_sq := center_sq3449
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3449.1
  jac_ok := checks3449.2.1
  accepted := checks3449.2.2

def tau3450 : RatBall :=
  ⟨⟨-31/640, 247/640⟩, 3/1280⟩
def center3450 : GaussianRat :=
  ⟨-4955369/125000000, 8807299/31250000⟩
def contact3450 : RatBall := localContactBall tau3450 center3450
def work3450 : RoundedTauEval :=
  evalTau precision tau3450 contact3450 logTwoBall

theorem center_sq3450 : (center3450.re : ℝ)^2 +
    (center3450.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3450]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3450 : work3450.theta.ok = true ∧
    work3450.jac.invOK = true ∧ acceptsUnitSq work3450.out = true := by
  norm_num [work3450, contact3450, tau3450, center3450, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3450 : CellCertificate where
  tauBall := tau3450
  contactCenter := center3450
  contactBall := contact3450
  work := work3450
  center_sq := center_sq3450
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3450.1
  jac_ok := checks3450.2.1
  accepted := checks3450.2.2

def tau3451 : RatBall :=
  ⟨⟨-29/640, 247/640⟩, 3/1280⟩
def center3451 : GaussianRat :=
  ⟨-18546463/500000000, 281946171/1000000000⟩
def contact3451 : RatBall := localContactBall tau3451 center3451
def work3451 : RoundedTauEval :=
  evalTau precision tau3451 contact3451 logTwoBall

theorem center_sq3451 : (center3451.re : ℝ)^2 +
    (center3451.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3451]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3451 : work3451.theta.ok = true ∧
    work3451.jac.invOK = true ∧ acceptsUnitSq work3451.out = true := by
  norm_num [work3451, contact3451, tau3451, center3451, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3451 : CellCertificate where
  tauBall := tau3451
  contactCenter := center3451
  contactBall := contact3451
  work := work3451
  center_sq := center_sq3451
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3451.1
  jac_ok := checks3451.2.1
  accepted := checks3451.2.2

def tau3452 : RatBall :=
  ⟨⟨-27/640, 49/128⟩, 3/1280⟩
def center3452 : GaussianRat :=
  ⟨-1076269/31250000, 69875701/250000000⟩
def contact3452 : RatBall := localContactBall tau3452 center3452
def work3452 : RoundedTauEval :=
  evalTau precision tau3452 contact3452 logTwoBall

theorem center_sq3452 : (center3452.re : ℝ)^2 +
    (center3452.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3452]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3452 : work3452.theta.ok = true ∧
    work3452.jac.invOK = true ∧ acceptsUnitSq work3452.out = true := by
  norm_num [work3452, contact3452, tau3452, center3452, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3452 : CellCertificate where
  tauBall := tau3452
  contactCenter := center3452
  contactBall := contact3452
  work := work3452
  center_sq := center_sq3452
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3452.1
  jac_ok := checks3452.2.1
  accepted := checks3452.2.2

def tau3453 : RatBall :=
  ⟨⟨-5/128, 49/128⟩, 3/1280⟩
def center3453 : GaussianRat :=
  ⟨-31895051/1000000000, 13979961/50000000⟩
def contact3453 : RatBall := localContactBall tau3453 center3453
def work3453 : RoundedTauEval :=
  evalTau precision tau3453 contact3453 logTwoBall

theorem center_sq3453 : (center3453.re : ℝ)^2 +
    (center3453.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3453]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3453 : work3453.theta.ok = true ∧
    work3453.jac.invOK = true ∧ acceptsUnitSq work3453.out = true := by
  norm_num [work3453, contact3453, tau3453, center3453, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3453 : CellCertificate where
  tauBall := tau3453
  contactCenter := center3453
  contactBall := contact3453
  work := work3453
  center_sq := center_sq3453
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3453.1
  jac_ok := checks3453.2.1
  accepted := checks3453.2.2

def tau3454 : RatBall :=
  ⟨⟨-27/640, 247/640⟩, 3/1280⟩
def center3454 : GaussianRat :=
  ⟨-34541389/1000000000, 56410273/200000000⟩
def contact3454 : RatBall := localContactBall tau3454 center3454
def work3454 : RoundedTauEval :=
  evalTau precision tau3454 contact3454 logTwoBall

theorem center_sq3454 : (center3454.re : ℝ)^2 +
    (center3454.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3454]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3454 : work3454.theta.ok = true ∧
    work3454.jac.invOK = true ∧ acceptsUnitSq work3454.out = true := by
  norm_num [work3454, contact3454, tau3454, center3454, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3454 : CellCertificate where
  tauBall := tau3454
  contactCenter := center3454
  contactBall := contact3454
  work := work3454
  center_sq := center_sq3454
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3454.1
  jac_ok := checks3454.2.1
  accepted := checks3454.2.2

def tau3455 : RatBall :=
  ⟨⟨-5/128, 247/640⟩, 3/1280⟩
def center3455 : GaussianRat :=
  ⟨-7997111/250000000, 282149129/1000000000⟩
def contact3455 : RatBall := localContactBall tau3455 center3455
def work3455 : RoundedTauEval :=
  evalTau precision tau3455 contact3455 logTwoBall

theorem center_sq3455 : (center3455.re : ℝ)^2 +
    (center3455.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3455]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3455 : work3455.theta.ok = true ∧
    work3455.jac.invOK = true ∧ acceptsUnitSq work3455.out = true := by
  norm_num [work3455, contact3455, tau3455, center3455, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3455 : CellCertificate where
  tauBall := tau3455
  contactCenter := center3455
  contactBall := contact3455
  work := work3455
  center_sq := center_sq3455
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3455.1
  jac_ok := checks3455.2.1
  accepted := checks3455.2.2

def cells : List CellCertificate := [cell3448, cell3449, cell3450, cell3451, cell3452, cell3453, cell3454, cell3455]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431
