import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3408 : RatBall :=
  ⟨⟨-9/128, 243/640⟩, 3/1280⟩
def center3408 : GaussianRat :=
  ⟨-456897/8000000, 17236447/62500000⟩
def contact3408 : RatBall := localContactBall tau3408 center3408
def work3408 : RoundedTauEval :=
  evalTau precision tau3408 contact3408 logTwoBall

theorem center_sq3408 : (center3408.re : ℝ)^2 +
    (center3408.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3408]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3408 : work3408.theta.ok = true ∧
    work3408.jac.invOK = true ∧ acceptsUnitSq work3408.out = true := by
  norm_num [work3408, contact3408, tau3408, center3408, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3408 : CellCertificate where
  tauBall := tau3408
  contactCenter := center3408
  contactBall := contact3408
  work := work3408
  center_sq := center_sq3408
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3408.1
  jac_ok := checks3408.2.1
  accepted := checks3408.2.2

def tau3409 : RatBall :=
  ⟨⟨-47/640, 49/128⟩, 3/1280⟩
def center3409 : GaussianRat :=
  ⟨-2392131/40000000, 55627861/200000000⟩
def contact3409 : RatBall := localContactBall tau3409 center3409
def work3409 : RoundedTauEval :=
  evalTau precision tau3409 contact3409 logTwoBall

theorem center_sq3409 : (center3409.re : ℝ)^2 +
    (center3409.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3409]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3409 : work3409.theta.ok = true ∧
    work3409.jac.invOK = true ∧ acceptsUnitSq work3409.out = true := by
  norm_num [work3409, contact3409, tau3409, center3409, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3409 : CellCertificate where
  tauBall := tau3409
  contactCenter := center3409
  contactBall := contact3409
  work := work3409
  center_sq := center_sq3409
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3409.1
  jac_ok := checks3409.2.1
  accepted := checks3409.2.2

def tau3410 : RatBall :=
  ⟨⟨-9/128, 49/128⟩, 3/1280⟩
def center3410 : GaussianRat :=
  ⟨-57276093/1000000000, 139153977/500000000⟩
def contact3410 : RatBall := localContactBall tau3410 center3410
def work3410 : RoundedTauEval :=
  evalTau precision tau3410 contact3410 logTwoBall

theorem center_sq3410 : (center3410.re : ℝ)^2 +
    (center3410.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3410]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3410 : work3410.theta.ok = true ∧
    work3410.jac.invOK = true ∧ acceptsUnitSq work3410.out = true := by
  norm_num [work3410, contact3410, tau3410, center3410, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3410 : CellCertificate where
  tauBall := tau3410
  contactCenter := center3410
  contactBall := contact3410
  work := work3410
  center_sq := center_sq3410
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3410.1
  jac_ok := checks3410.2.1
  accepted := checks3410.2.2

def tau3411 : RatBall :=
  ⟨⟨-47/640, 247/640⟩, 3/1280⟩
def center3411 : GaussianRat :=
  ⟨-59976659/1000000000, 70167217/250000000⟩
def contact3411 : RatBall := localContactBall tau3411 center3411
def work3411 : RoundedTauEval :=
  evalTau precision tau3411 contact3411 logTwoBall

theorem center_sq3411 : (center3411.re : ℝ)^2 +
    (center3411.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3411]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3411 : work3411.theta.ok = true ∧
    work3411.jac.invOK = true ∧ acceptsUnitSq work3411.out = true := by
  norm_num [work3411, contact3411, tau3411, center3411, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3411 : CellCertificate where
  tauBall := tau3411
  contactCenter := center3411
  contactBall := contact3411
  work := work3411
  center_sq := center_sq3411
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3411.1
  jac_ok := checks3411.2.1
  accepted := checks3411.2.2

def tau3412 : RatBall :=
  ⟨⟨-9/128, 247/640⟩, 3/1280⟩
def center3412 : GaussianRat :=
  ⟨-2872117/50000000, 14041993/50000000⟩
def contact3412 : RatBall := localContactBall tau3412 center3412
def work3412 : RoundedTauEval :=
  evalTau precision tau3412 contact3412 logTwoBall

theorem center_sq3412 : (center3412.re : ℝ)^2 +
    (center3412.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3412]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3412 : work3412.theta.ok = true ∧
    work3412.jac.invOK = true ∧ acceptsUnitSq work3412.out = true := by
  norm_num [work3412, contact3412, tau3412, center3412, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3412 : CellCertificate where
  tauBall := tau3412
  contactCenter := center3412
  contactBall := contact3412
  work := work3412
  center_sq := center_sq3412
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3412.1
  jac_ok := checks3412.2.1
  accepted := checks3412.2.2

def tau3413 : RatBall :=
  ⟨⟨-43/640, 49/128⟩, 3/1280⟩
def center3413 : GaussianRat :=
  ⟨-6843329/125000000, 556939/2000000⟩
def contact3413 : RatBall := localContactBall tau3413 center3413
def work3413 : RoundedTauEval :=
  evalTau precision tau3413 contact3413 logTwoBall

theorem center_sq3413 : (center3413.re : ℝ)^2 +
    (center3413.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3413]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3413 : work3413.theta.ok = true ∧
    work3413.jac.invOK = true ∧ acceptsUnitSq work3413.out = true := by
  norm_num [work3413, contact3413, tau3413, center3413, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3413 : CellCertificate where
  tauBall := tau3413
  contactCenter := center3413
  contactBall := contact3413
  work := work3413
  center_sq := center_sq3413
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3413.1
  jac_ok := checks3413.2.1
  accepted := checks3413.2.2

def tau3414 : RatBall :=
  ⟨⟨-41/640, 49/128⟩, 3/1280⟩
def center3414 : GaussianRat :=
  ⟨-13053747/250000000, 34827989/125000000⟩
def contact3414 : RatBall := localContactBall tau3414 center3414
def work3414 : RoundedTauEval :=
  evalTau precision tau3414 contact3414 logTwoBall

theorem center_sq3414 : (center3414.re : ℝ)^2 +
    (center3414.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3414]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3414 : work3414.theta.ok = true ∧
    work3414.jac.invOK = true ∧ acceptsUnitSq work3414.out = true := by
  norm_num [work3414, contact3414, tau3414, center3414, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3414 : CellCertificate where
  tauBall := tau3414
  contactCenter := center3414
  contactBall := contact3414
  work := work3414
  center_sq := center_sq3414
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3414.1
  jac_ok := checks3414.2.1
  accepted := checks3414.2.2

def tau3415 : RatBall :=
  ⟨⟨-43/640, 247/640⟩, 3/1280⟩
def center3415 : GaussianRat :=
  ⟨-3431607/62500000, 70250913/250000000⟩
def contact3415 : RatBall := localContactBall tau3415 center3415
def work3415 : RoundedTauEval :=
  evalTau precision tau3415 contact3415 logTwoBall

theorem center_sq3415 : (center3415.re : ℝ)^2 +
    (center3415.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3415]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3415 : work3415.theta.ok = true ∧
    work3415.jac.invOK = true ∧ acceptsUnitSq work3415.out = true := by
  norm_num [work3415, contact3415, tau3415, center3415, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3415 : CellCertificate where
  tauBall := tau3415
  contactCenter := center3415
  contactBall := contact3415
  work := work3415
  center_sq := center_sq3415
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3415.1
  jac_ok := checks3415.2.1
  accepted := checks3415.2.2

def cells : List CellCertificate := [cell3408, cell3409, cell3410, cell3411, cell3412, cell3413, cell3414, cell3415]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426
