import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3504 : RatBall :=
  ⟨⟨-11/640, 253/640⟩, 3/1280⟩
def center3504 : GaussianRat :=
  ⟨-7107163/500000000, 290339131/1000000000⟩
def contact3504 : RatBall := localContactBall tau3504 center3504
def work3504 : RoundedTauEval :=
  evalTau precision tau3504 contact3504 logTwoBall

theorem center_sq3504 : (center3504.re : ℝ)^2 +
    (center3504.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3504]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3504 : work3504.theta.ok = true ∧
    work3504.jac.invOK = true ∧ acceptsUnitSq work3504.out = true := by
  norm_num [work3504, contact3504, tau3504, center3504, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3504 : CellCertificate where
  tauBall := tau3504
  contactCenter := center3504
  contactBall := contact3504
  work := work3504
  center_sq := center_sq3504
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3504.1
  jac_ok := checks3504.2.1
  accepted := checks3504.2.2

def tau3505 : RatBall :=
  ⟨⟨-9/640, 253/640⟩, 3/1280⟩
def center3505 : GaussianRat :=
  ⟨-5815363/500000000, 145189259/500000000⟩
def contact3505 : RatBall := localContactBall tau3505 center3505
def work3505 : RoundedTauEval :=
  evalTau precision tau3505 contact3505 logTwoBall

theorem center_sq3505 : (center3505.re : ℝ)^2 +
    (center3505.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3505]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3505 : work3505.theta.ok = true ∧
    work3505.jac.invOK = true ∧ acceptsUnitSq work3505.out = true := by
  norm_num [work3505, contact3505, tau3505, center3505, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3505 : CellCertificate where
  tauBall := tau3505
  contactCenter := center3505
  contactBall := contact3505
  work := work3505
  center_sq := center_sq3505
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3505.1
  jac_ok := checks3505.2.1
  accepted := checks3505.2.2

def tau3506 : RatBall :=
  ⟨⟨-11/640, 51/128⟩, 3/1280⟩
def center3506 : GaussianRat :=
  ⟨-3564487/250000000, 73231599/250000000⟩
def contact3506 : RatBall := localContactBall tau3506 center3506
def work3506 : RoundedTauEval :=
  evalTau precision tau3506 contact3506 logTwoBall

theorem center_sq3506 : (center3506.re : ℝ)^2 +
    (center3506.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3506]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3506 : work3506.theta.ok = true ∧
    work3506.jac.invOK = true ∧ acceptsUnitSq work3506.out = true := by
  norm_num [work3506, contact3506, tau3506, center3506, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3506 : CellCertificate where
  tauBall := tau3506
  contactCenter := center3506
  contactBall := contact3506
  work := work3506
  center_sq := center_sq3506
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3506.1
  jac_ok := checks3506.2.1
  accepted := checks3506.2.2

def tau3507 : RatBall :=
  ⟨⟨-9/640, 51/128⟩, 3/1280⟩
def center3507 : GaussianRat :=
  ⟨-11666429/1000000000, 4577599/15625000⟩
def contact3507 : RatBall := localContactBall tau3507 center3507
def work3507 : RoundedTauEval :=
  evalTau precision tau3507 contact3507 logTwoBall

theorem center_sq3507 : (center3507.re : ℝ)^2 +
    (center3507.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3507]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3507 : work3507.theta.ok = true ∧
    work3507.jac.invOK = true ∧ acceptsUnitSq work3507.out = true := by
  norm_num [work3507, contact3507, tau3507, center3507, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3507 : CellCertificate where
  tauBall := tau3507
  contactCenter := center3507
  contactBall := contact3507
  work := work3507
  center_sq := center_sq3507
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3507.1
  jac_ok := checks3507.2.1
  accepted := checks3507.2.2

def tau3508 : RatBall :=
  ⟨⟨-7/640, 249/640⟩, 3/1280⟩
def center3508 : GaussianRat :=
  ⟨-2248057/250000000, 142628517/500000000⟩
def contact3508 : RatBall := localContactBall tau3508 center3508
def work3508 : RoundedTauEval :=
  evalTau precision tau3508 contact3508 logTwoBall

theorem center_sq3508 : (center3508.re : ℝ)^2 +
    (center3508.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3508]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3508 : work3508.theta.ok = true ∧
    work3508.jac.invOK = true ∧ acceptsUnitSq work3508.out = true := by
  norm_num [work3508, contact3508, tau3508, center3508, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3508 : CellCertificate where
  tauBall := tau3508
  contactCenter := center3508
  contactBall := contact3508
  work := work3508
  center_sq := center_sq3508
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3508.1
  jac_ok := checks3508.2.1
  accepted := checks3508.2.2

def tau3509 : RatBall :=
  ⟨⟨-1/128, 249/640⟩, 3/1280⟩
def center3509 : GaussianRat :=
  ⟨-6423287/1000000000, 285280029/1000000000⟩
def contact3509 : RatBall := localContactBall tau3509 center3509
def work3509 : RoundedTauEval :=
  evalTau precision tau3509 contact3509 logTwoBall

theorem center_sq3509 : (center3509.re : ℝ)^2 +
    (center3509.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3509]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3509 : work3509.theta.ok = true ∧
    work3509.jac.invOK = true ∧ acceptsUnitSq work3509.out = true := by
  norm_num [work3509, contact3509, tau3509, center3509, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3509 : CellCertificate where
  tauBall := tau3509
  contactCenter := center3509
  contactBall := contact3509
  work := work3509
  center_sq := center_sq3509
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3509.1
  jac_ok := checks3509.2.1
  accepted := checks3509.2.2

def tau3510 : RatBall :=
  ⟨⟨-7/640, 251/640⟩, 3/1280⟩
def center3510 : GaussianRat :=
  ⟨-9019241/1000000000, 287829653/1000000000⟩
def contact3510 : RatBall := localContactBall tau3510 center3510
def work3510 : RoundedTauEval :=
  evalTau precision tau3510 contact3510 logTwoBall

theorem center_sq3510 : (center3510.re : ℝ)^2 +
    (center3510.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3510]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3510 : work3510.theta.ok = true ∧
    work3510.jac.invOK = true ∧ acceptsUnitSq work3510.out = true := by
  norm_num [work3510, contact3510, tau3510, center3510, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3510 : CellCertificate where
  tauBall := tau3510
  contactCenter := center3510
  contactBall := contact3510
  work := work3510
  center_sq := center_sq3510
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3510.1
  jac_ok := checks3510.2.1
  accepted := checks3510.2.2

def tau3511 : RatBall :=
  ⟨⟨-1/128, 251/640⟩, 3/1280⟩
def center3511 : GaussianRat :=
  ⟨-3221293/500000000, 287852971/1000000000⟩
def contact3511 : RatBall := localContactBall tau3511 center3511
def work3511 : RoundedTauEval :=
  evalTau precision tau3511 contact3511 logTwoBall

theorem center_sq3511 : (center3511.re : ℝ)^2 +
    (center3511.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3511]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3511 : work3511.theta.ok = true ∧
    work3511.jac.invOK = true ∧ acceptsUnitSq work3511.out = true := by
  norm_num [work3511, contact3511, tau3511, center3511, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3511 : CellCertificate where
  tauBall := tau3511
  contactCenter := center3511
  contactBall := contact3511
  work := work3511
  center_sq := center_sq3511
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3511.1
  jac_ok := checks3511.2.1
  accepted := checks3511.2.2

def cells : List CellCertificate := [cell3504, cell3505, cell3506, cell3507, cell3508, cell3509, cell3510, cell3511]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438
