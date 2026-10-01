import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3424 : RatBall :=
  ⟨⟨-33/640, 247/640⟩, 3/1280⟩
def center3424 : GaussianRat :=
  ⟨-8438273/200000000, 281713577/1000000000⟩
def contact3424 : RatBall := localContactBall tau3424 center3424
def work3424 : RoundedTauEval :=
  evalTau precision tau3424 contact3424 logTwoBall

theorem center_sq3424 : (center3424.re : ℝ)^2 +
    (center3424.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3424]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3424 : work3424.theta.ok = true ∧
    work3424.jac.invOK = true ∧ acceptsUnitSq work3424.out = true := by
  norm_num [work3424, contact3424, tau3424, center3424, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3424 : CellCertificate where
  tauBall := tau3424
  contactCenter := center3424
  contactBall := contact3424
  work := work3424
  center_sq := center_sq3424
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3424.1
  jac_ok := checks3424.2.1
  accepted := checks3424.2.2

def tau3425 : RatBall :=
  ⟨⟨-47/640, 249/640⟩, 3/1280⟩
def center3425 : GaussianRat :=
  ⟨-60152449/1000000000, 283205599/1000000000⟩
def contact3425 : RatBall := localContactBall tau3425 center3425
def work3425 : RoundedTauEval :=
  evalTau precision tau3425 contact3425 logTwoBall

theorem center_sq3425 : (center3425.re : ℝ)^2 +
    (center3425.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3425]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3425 : work3425.theta.ok = true ∧
    work3425.jac.invOK = true ∧ acceptsUnitSq work3425.out = true := by
  norm_num [work3425, contact3425, tau3425, center3425, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3425 : CellCertificate where
  tauBall := tau3425
  contactCenter := center3425
  contactBall := contact3425
  work := work3425
  center_sq := center_sq3425
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3425.1
  jac_ok := checks3425.2.1
  accepted := checks3425.2.2

def tau3426 : RatBall :=
  ⟨⟨-9/128, 249/640⟩, 3/1280⟩
def center3426 : GaussianRat :=
  ⟨-28805449/500000000, 141689483/500000000⟩
def contact3426 : RatBall := localContactBall tau3426 center3426
def work3426 : RoundedTauEval :=
  evalTau precision tau3426 contact3426 logTwoBall

theorem center_sq3426 : (center3426.re : ℝ)^2 +
    (center3426.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3426]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3426 : work3426.theta.ok = true ∧
    work3426.jac.invOK = true ∧ acceptsUnitSq work3426.out = true := by
  norm_num [work3426, contact3426, tau3426, center3426, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3426 : CellCertificate where
  tauBall := tau3426
  contactCenter := center3426
  contactBall := contact3426
  work := work3426
  center_sq := center_sq3426
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3426.1
  jac_ok := checks3426.2.1
  accepted := checks3426.2.2

def tau3427 : RatBall :=
  ⟨⟨-47/640, 251/640⟩, 3/1280⟩
def center3427 : GaussianRat :=
  ⟨-1508267/25000000, 71437399/250000000⟩
def contact3427 : RatBall := localContactBall tau3427 center3427
def work3427 : RoundedTauEval :=
  evalTau precision tau3427 contact3427 logTwoBall

theorem center_sq3427 : (center3427.re : ℝ)^2 +
    (center3427.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3427]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3427 : work3427.theta.ok = true ∧
    work3427.jac.invOK = true ∧ acceptsUnitSq work3427.out = true := by
  norm_num [work3427, contact3427, tau3427, center3427, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3427 : CellCertificate where
  tauBall := tau3427
  contactCenter := center3427
  contactBall := contact3427
  work := work3427
  center_sq := center_sq3427
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3427.1
  jac_ok := checks3427.2.1
  accepted := checks3427.2.2

def tau3428 : RatBall :=
  ⟨⟨-9/128, 251/640⟩, 3/1280⟩
def center3428 : GaussianRat :=
  ⟨-57781797/1000000000, 285925371/1000000000⟩
def contact3428 : RatBall := localContactBall tau3428 center3428
def work3428 : RoundedTauEval :=
  evalTau precision tau3428 contact3428 logTwoBall

theorem center_sq3428 : (center3428.re : ℝ)^2 +
    (center3428.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3428]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3428 : work3428.theta.ok = true ∧
    work3428.jac.invOK = true ∧ acceptsUnitSq work3428.out = true := by
  norm_num [work3428, contact3428, tau3428, center3428, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3428 : CellCertificate where
  tauBall := tau3428
  contactCenter := center3428
  contactBall := contact3428
  work := work3428
  center_sq := center_sq3428
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3428.1
  jac_ok := checks3428.2.1
  accepted := checks3428.2.2

def tau3429 : RatBall :=
  ⟨⟨-43/640, 249/640⟩, 3/1280⟩
def center3429 : GaussianRat :=
  ⟨-13766751/250000000, 141772517/500000000⟩
def contact3429 : RatBall := localContactBall tau3429 center3429
def work3429 : RoundedTauEval :=
  evalTau precision tau3429 contact3429 logTwoBall

theorem center_sq3429 : (center3429.re : ℝ)^2 +
    (center3429.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3429]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3429 : work3429.theta.ok = true ∧
    work3429.jac.invOK = true ∧ acceptsUnitSq work3429.out = true := by
  norm_num [work3429, contact3429, tau3429, center3429, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3429 : CellCertificate where
  tauBall := tau3429
  contactCenter := center3429
  contactBall := contact3429
  work := work3429
  center_sq := center_sq3429
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3429.1
  jac_ok := checks3429.2.1
  accepted := checks3429.2.2

def tau3430 : RatBall :=
  ⟨⟨-41/640, 249/640⟩, 3/1280⟩
def center3430 : GaussianRat :=
  ⟨-13130217/250000000, 283703773/1000000000⟩
def contact3430 : RatBall := localContactBall tau3430 center3430
def work3430 : RoundedTauEval :=
  evalTau precision tau3430 contact3430 logTwoBall

theorem center_sq3430 : (center3430.re : ℝ)^2 +
    (center3430.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3430]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3430 : work3430.theta.ok = true ∧
    work3430.jac.invOK = true ∧ acceptsUnitSq work3430.out = true := by
  norm_num [work3430, contact3430, tau3430, center3430, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3430 : CellCertificate where
  tauBall := tau3430
  contactCenter := center3430
  contactBall := contact3430
  work := work3430
  center_sq := center_sq3430
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3430.1
  jac_ok := checks3430.2.1
  accepted := checks3430.2.2

def tau3431 : RatBall :=
  ⟨⟨-43/640, 251/640⟩, 3/1280⟩
def center3431 : GaussianRat :=
  ⟨-2761527/50000000, 286093747/1000000000⟩
def contact3431 : RatBall := localContactBall tau3431 center3431
def work3431 : RoundedTauEval :=
  evalTau precision tau3431 contact3431 logTwoBall

theorem center_sq3431 : (center3431.re : ℝ)^2 +
    (center3431.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3431]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3431 : work3431.theta.ok = true ∧
    work3431.jac.invOK = true ∧ acceptsUnitSq work3431.out = true := by
  norm_num [work3431, contact3431, tau3431, center3431, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3431 : CellCertificate where
  tauBall := tau3431
  contactCenter := center3431
  contactBall := contact3431
  work := work3431
  center_sq := center_sq3431
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3431.1
  jac_ok := checks3431.2.1
  accepted := checks3431.2.2

def cells : List CellCertificate := [cell3424, cell3425, cell3426, cell3427, cell3428, cell3429, cell3430, cell3431]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428
