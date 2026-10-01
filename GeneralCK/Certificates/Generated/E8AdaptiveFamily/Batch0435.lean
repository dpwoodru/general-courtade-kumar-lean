import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3480 : RatBall :=
  ⟨⟨-19/640, 249/640⟩, 3/1280⟩
def center3480 : GaussianRat :=
  ⟨-6098577/250000000, 142479251/500000000⟩
def contact3480 : RatBall := localContactBall tau3480 center3480
def work3480 : RoundedTauEval :=
  evalTau precision tau3480 contact3480 logTwoBall

theorem center_sq3480 : (center3480.re : ℝ)^2 +
    (center3480.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3480]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3480 : work3480.theta.ok = true ∧
    work3480.jac.invOK = true ∧ acceptsUnitSq work3480.out = true := by
  norm_num [work3480, contact3480, tau3480, center3480, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3480 : CellCertificate where
  tauBall := tau3480
  contactCenter := center3480
  contactBall := contact3480
  work := work3480
  center_sq := center_sq3480
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3480.1
  jac_ok := checks3480.2.1
  accepted := checks3480.2.2

def tau3481 : RatBall :=
  ⟨⟨-17/640, 249/640⟩, 3/1280⟩
def center3481 : GaussianRat :=
  ⟨-10914601/500000000, 285027327/1000000000⟩
def contact3481 : RatBall := localContactBall tau3481 center3481
def work3481 : RoundedTauEval :=
  evalTau precision tau3481 contact3481 logTwoBall

theorem center_sq3481 : (center3481.re : ℝ)^2 +
    (center3481.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3481]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3481 : work3481.theta.ok = true ∧
    work3481.jac.invOK = true ∧ acceptsUnitSq work3481.out = true := by
  norm_num [work3481, contact3481, tau3481, center3481, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3481 : CellCertificate where
  tauBall := tau3481
  contactCenter := center3481
  contactBall := contact3481
  work := work3481
  center_sq := center_sq3481
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3481.1
  jac_ok := checks3481.2.1
  accepted := checks3481.2.2

def tau3482 : RatBall :=
  ⟨⟨-19/640, 251/640⟩, 3/1280⟩
def center3482 : GaussianRat :=
  ⟨-12233721/500000000, 287526937/1000000000⟩
def contact3482 : RatBall := localContactBall tau3482 center3482
def work3482 : RoundedTauEval :=
  evalTau precision tau3482 contact3482 logTwoBall

theorem center_sq3482 : (center3482.re : ℝ)^2 +
    (center3482.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3482]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3482 : work3482.theta.ok = true ∧
    work3482.jac.invOK = true ∧ acceptsUnitSq work3482.out = true := by
  norm_num [work3482, contact3482, tau3482, center3482, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3482 : CellCertificate where
  tauBall := tau3482
  contactCenter := center3482
  contactBall := contact3482
  work := work3482
  center_sq := center_sq3482
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3482.1
  jac_ok := checks3482.2.1
  accepted := checks3482.2.2

def tau3483 : RatBall :=
  ⟨⟨-17/640, 251/640⟩, 3/1280⟩
def center3483 : GaussianRat :=
  ⟨-21894677/1000000000, 143798363/500000000⟩
def contact3483 : RatBall := localContactBall tau3483 center3483
def work3483 : RoundedTauEval :=
  evalTau precision tau3483 contact3483 logTwoBall

theorem center_sq3483 : (center3483.re : ℝ)^2 +
    (center3483.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3483]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3483 : work3483.theta.ok = true ∧
    work3483.jac.invOK = true ∧ acceptsUnitSq work3483.out = true := by
  norm_num [work3483, contact3483, tau3483, center3483, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3483 : CellCertificate where
  tauBall := tau3483
  contactCenter := center3483
  contactBall := contact3483
  work := work3483
  center_sq := center_sq3483
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3483.1
  jac_ok := checks3483.2.1
  accepted := checks3483.2.2

def tau3484 : RatBall :=
  ⟨⟨-23/640, 253/640⟩, 3/1280⟩
def center3484 : GaussianRat :=
  ⟨-14849721/500000000, 7248453/25000000⟩
def contact3484 : RatBall := localContactBall tau3484 center3484
def work3484 : RoundedTauEval :=
  evalTau precision tau3484 contact3484 logTwoBall

theorem center_sq3484 : (center3484.re : ℝ)^2 +
    (center3484.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3484]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3484 : work3484.theta.ok = true ∧
    work3484.jac.invOK = true ∧ acceptsUnitSq work3484.out = true := by
  norm_num [work3484, contact3484, tau3484, center3484, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3484 : CellCertificate where
  tauBall := tau3484
  contactCenter := center3484
  contactBall := contact3484
  work := work3484
  center_sq := center_sq3484
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3484.1
  jac_ok := checks3484.2.1
  accepted := checks3484.2.2

def tau3485 : RatBall :=
  ⟨⟨-21/640, 253/640⟩, 3/1280⟩
def center3485 : GaussianRat :=
  ⟨-5424219/200000000, 290024499/1000000000⟩
def contact3485 : RatBall := localContactBall tau3485 center3485
def work3485 : RoundedTauEval :=
  evalTau precision tau3485 contact3485 logTwoBall

theorem center_sq3485 : (center3485.re : ℝ)^2 +
    (center3485.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3485]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3485 : work3485.theta.ok = true ∧
    work3485.jac.invOK = true ∧ acceptsUnitSq work3485.out = true := by
  norm_num [work3485, contact3485, tau3485, center3485, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3485 : CellCertificate where
  tauBall := tau3485
  contactCenter := center3485
  contactBall := contact3485
  work := work3485
  center_sq := center_sq3485
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3485.1
  jac_ok := checks3485.2.1
  accepted := checks3485.2.2

def tau3486 : RatBall :=
  ⟨⟨-23/640, 51/128⟩, 3/1280⟩
def center3486 : GaussianRat :=
  ⟨-5958069/200000000, 292519767/1000000000⟩
def contact3486 : RatBall := localContactBall tau3486 center3486
def work3486 : RoundedTauEval :=
  evalTau precision tau3486 contact3486 logTwoBall

theorem center_sq3486 : (center3486.re : ℝ)^2 +
    (center3486.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3486]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3486 : work3486.theta.ok = true ∧
    work3486.jac.invOK = true ∧ acceptsUnitSq work3486.out = true := by
  norm_num [work3486, contact3486, tau3486, center3486, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3486 : CellCertificate where
  tauBall := tau3486
  contactCenter := center3486
  contactBall := contact3486
  work := work3486
  center_sq := center_sq3486
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3486.1
  jac_ok := checks3486.2.1
  accepted := checks3486.2.2

def tau3487 : RatBall :=
  ⟨⟨-21/640, 51/128⟩, 3/1280⟩
def center3487 : GaussianRat :=
  ⟨-27204153/1000000000, 58521471/200000000⟩
def contact3487 : RatBall := localContactBall tau3487 center3487
def work3487 : RoundedTauEval :=
  evalTau precision tau3487 contact3487 logTwoBall

theorem center_sq3487 : (center3487.re : ℝ)^2 +
    (center3487.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3487]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3487 : work3487.theta.ok = true ∧
    work3487.jac.invOK = true ∧ acceptsUnitSq work3487.out = true := by
  norm_num [work3487, contact3487, tau3487, center3487, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3487 : CellCertificate where
  tauBall := tau3487
  contactCenter := center3487
  contactBall := contact3487
  work := work3487
  center_sq := center_sq3487
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3487.1
  jac_ok := checks3487.2.1
  accepted := checks3487.2.2

def cells : List CellCertificate := [cell3480, cell3481, cell3482, cell3483, cell3484, cell3485, cell3486, cell3487]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435
