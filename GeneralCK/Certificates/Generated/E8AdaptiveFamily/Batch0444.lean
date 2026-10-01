import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3552 : RatBall :=
  ⟨⟨13/640, 253/640⟩, 3/1280⟩
def center3552 : GaussianRat :=
  ⟨16797323/1000000000, 290291883/1000000000⟩
def contact3552 : RatBall := localContactBall tau3552 center3552
def work3552 : RoundedTauEval :=
  evalTau precision tau3552 contact3552 logTwoBall

theorem center_sq3552 : (center3552.re : ℝ)^2 +
    (center3552.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3552]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3552 : work3552.theta.ok = true ∧
    work3552.jac.invOK = true ∧ acceptsUnitSq work3552.out = true := by
  norm_num [work3552, contact3552, tau3552, center3552, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3552 : CellCertificate where
  tauBall := tau3552
  contactCenter := center3552
  contactBall := contact3552
  work := work3552
  center_sq := center_sq3552
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3552.1
  jac_ok := checks3552.2.1
  accepted := checks3552.2.2

def tau3553 : RatBall :=
  ⟨⟨3/128, 253/640⟩, 3/1280⟩
def center3553 : GaussianRat :=
  ⟨19379607/1000000000, 58047357/200000000⟩
def contact3553 : RatBall := localContactBall tau3553 center3553
def work3553 : RoundedTauEval :=
  evalTau precision tau3553 contact3553 logTwoBall

theorem center_sq3553 : (center3553.re : ℝ)^2 +
    (center3553.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3553]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3553 : work3553.theta.ok = true ∧
    work3553.jac.invOK = true ∧ acceptsUnitSq work3553.out = true := by
  norm_num [work3553, contact3553, tau3553, center3553, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3553 : CellCertificate where
  tauBall := tau3553
  contactCenter := center3553
  contactBall := contact3553
  work := work3553
  center_sq := center_sq3553
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3553.1
  jac_ok := checks3553.2.1
  accepted := checks3553.2.2

def tau3554 : RatBall :=
  ⟨⟨13/640, 51/128⟩, 3/1280⟩
def center3554 : GaussianRat :=
  ⟨3369771/200000000, 146439243/500000000⟩
def contact3554 : RatBall := localContactBall tau3554 center3554
def work3554 : RoundedTauEval :=
  evalTau precision tau3554 contact3554 logTwoBall

theorem center_sq3554 : (center3554.re : ℝ)^2 +
    (center3554.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3554]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3554 : work3554.theta.ok = true ∧
    work3554.jac.invOK = true ∧ acceptsUnitSq work3554.out = true := by
  norm_num [work3554, contact3554, tau3554, center3554, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3554 : CellCertificate where
  tauBall := tau3554
  contactCenter := center3554
  contactBall := contact3554
  work := work3554
  center_sq := center_sq3554
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3554.1
  jac_ok := checks3554.2.1
  accepted := checks3554.2.2

def tau3555 : RatBall :=
  ⟨⟨3/128, 51/128⟩, 3/1280⟩
def center3555 : GaussianRat :=
  ⟨60747/3125000, 58564523/200000000⟩
def contact3555 : RatBall := localContactBall tau3555 center3555
def work3555 : RoundedTauEval :=
  evalTau precision tau3555 contact3555 logTwoBall

theorem center_sq3555 : (center3555.re : ℝ)^2 +
    (center3555.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3555]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3555 : work3555.theta.ok = true ∧
    work3555.jac.invOK = true ∧ acceptsUnitSq work3555.out = true := by
  norm_num [work3555, contact3555, tau3555, center3555, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3555 : CellCertificate where
  tauBall := tau3555
  contactCenter := center3555
  contactBall := contact3555
  work := work3555
  center_sq := center_sq3555
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3555.1
  jac_ok := checks3555.2.1
  accepted := checks3555.2.2

def tau3556 : RatBall :=
  ⟨⟨21/640, 49/128⟩, 3/1280⟩
def center3556 : GaussianRat :=
  ⟨6700043/250000000, 139884999/500000000⟩
def contact3556 : RatBall := localContactBall tau3556 center3556
def work3556 : RoundedTauEval :=
  evalTau precision tau3556 contact3556 logTwoBall

theorem center_sq3556 : (center3556.re : ℝ)^2 +
    (center3556.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3556]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3556 : work3556.theta.ok = true ∧
    work3556.jac.invOK = true ∧ acceptsUnitSq work3556.out = true := by
  norm_num [work3556, contact3556, tau3556, center3556, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3556 : CellCertificate where
  tauBall := tau3556
  contactCenter := center3556
  contactBall := contact3556
  work := work3556
  center_sq := center_sq3556
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3556.1
  jac_ok := checks3556.2.1
  accepted := checks3556.2.2

def tau3557 : RatBall :=
  ⟨⟨23/640, 49/128⟩, 3/1280⟩
def center3557 : GaussianRat :=
  ⟨7337051/250000000, 279688291/1000000000⟩
def contact3557 : RatBall := localContactBall tau3557 center3557
def work3557 : RoundedTauEval :=
  evalTau precision tau3557 contact3557 logTwoBall

theorem center_sq3557 : (center3557.re : ℝ)^2 +
    (center3557.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3557]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3557 : work3557.theta.ok = true ∧
    work3557.jac.invOK = true ∧ acceptsUnitSq work3557.out = true := by
  norm_num [work3557, contact3557, tau3557, center3557, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3557 : CellCertificate where
  tauBall := tau3557
  contactCenter := center3557
  contactBall := contact3557
  work := work3557
  center_sq := center_sq3557
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3557.1
  jac_ok := checks3557.2.1
  accepted := checks3557.2.2

def tau3558 : RatBall :=
  ⟨⟨21/640, 247/640⟩, 3/1280⟩
def center3558 : GaussianRat :=
  ⟨26878737/1000000000, 282322297/1000000000⟩
def contact3558 : RatBall := localContactBall tau3558 center3558
def work3558 : RoundedTauEval :=
  evalTau precision tau3558 contact3558 logTwoBall

theorem center_sq3558 : (center3558.re : ℝ)^2 +
    (center3558.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3558]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3558 : work3558.theta.ok = true ∧
    work3558.jac.invOK = true ∧ acceptsUnitSq work3558.out = true := by
  norm_num [work3558, contact3558, tau3558, center3558, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3558 : CellCertificate where
  tauBall := tau3558
  contactCenter := center3558
  contactBall := contact3558
  work := work3558
  center_sq := center_sq3558
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3558.1
  jac_ok := checks3558.2.1
  accepted := checks3558.2.2

def tau3559 : RatBall :=
  ⟨⟨23/640, 247/640⟩, 3/1280⟩
def center3559 : GaussianRat :=
  ⟨1839637/62500000, 141119723/500000000⟩
def contact3559 : RatBall := localContactBall tau3559 center3559
def work3559 : RoundedTauEval :=
  evalTau precision tau3559 contact3559 logTwoBall

theorem center_sq3559 : (center3559.re : ℝ)^2 +
    (center3559.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3559]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3559 : work3559.theta.ok = true ∧
    work3559.jac.invOK = true ∧ acceptsUnitSq work3559.out = true := by
  norm_num [work3559, contact3559, tau3559, center3559, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3559 : CellCertificate where
  tauBall := tau3559
  contactCenter := center3559
  contactBall := contact3559
  work := work3559
  center_sq := center_sq3559
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3559.1
  jac_ok := checks3559.2.1
  accepted := checks3559.2.2

def cells : List CellCertificate := [cell3552, cell3553, cell3554, cell3555, cell3556, cell3557, cell3558, cell3559]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444
