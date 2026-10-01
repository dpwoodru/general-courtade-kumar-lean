import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3568 : RatBall :=
  ⟨⟨17/640, 249/640⟩, 3/1280⟩
def center3568 : GaussianRat :=
  ⟨10914601/500000000, 285027327/1000000000⟩
def contact3568 : RatBall := localContactBall tau3568 center3568
def work3568 : RoundedTauEval :=
  evalTau precision tau3568 contact3568 logTwoBall

theorem center_sq3568 : (center3568.re : ℝ)^2 +
    (center3568.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3568]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3568 : work3568.theta.ok = true ∧
    work3568.jac.invOK = true ∧ acceptsUnitSq work3568.out = true := by
  norm_num [work3568, contact3568, tau3568, center3568, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3568 : CellCertificate where
  tauBall := tau3568
  contactCenter := center3568
  contactBall := contact3568
  work := work3568
  center_sq := center_sq3568
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3568.1
  jac_ok := checks3568.2.1
  accepted := checks3568.2.2

def tau3569 : RatBall :=
  ⟨⟨19/640, 249/640⟩, 3/1280⟩
def center3569 : GaussianRat :=
  ⟨6098577/250000000, 142479251/500000000⟩
def contact3569 : RatBall := localContactBall tau3569 center3569
def work3569 : RoundedTauEval :=
  evalTau precision tau3569 contact3569 logTwoBall

theorem center_sq3569 : (center3569.re : ℝ)^2 +
    (center3569.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3569]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3569 : work3569.theta.ok = true ∧
    work3569.jac.invOK = true ∧ acceptsUnitSq work3569.out = true := by
  norm_num [work3569, contact3569, tau3569, center3569, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3569 : CellCertificate where
  tauBall := tau3569
  contactCenter := center3569
  contactBall := contact3569
  work := work3569
  center_sq := center_sq3569
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3569.1
  jac_ok := checks3569.2.1
  accepted := checks3569.2.2

def tau3570 : RatBall :=
  ⟨⟨17/640, 251/640⟩, 3/1280⟩
def center3570 : GaussianRat :=
  ⟨21894677/1000000000, 143798363/500000000⟩
def contact3570 : RatBall := localContactBall tau3570 center3570
def work3570 : RoundedTauEval :=
  evalTau precision tau3570 contact3570 logTwoBall

theorem center_sq3570 : (center3570.re : ℝ)^2 +
    (center3570.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3570]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3570 : work3570.theta.ok = true ∧
    work3570.jac.invOK = true ∧ acceptsUnitSq work3570.out = true := by
  norm_num [work3570, contact3570, tau3570, center3570, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3570 : CellCertificate where
  tauBall := tau3570
  contactCenter := center3570
  contactBall := contact3570
  work := work3570
  center_sq := center_sq3570
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3570.1
  jac_ok := checks3570.2.1
  accepted := checks3570.2.2

def tau3571 : RatBall :=
  ⟨⟨19/640, 251/640⟩, 3/1280⟩
def center3571 : GaussianRat :=
  ⟨12233721/500000000, 287526937/1000000000⟩
def contact3571 : RatBall := localContactBall tau3571 center3571
def work3571 : RoundedTauEval :=
  evalTau precision tau3571 contact3571 logTwoBall

theorem center_sq3571 : (center3571.re : ℝ)^2 +
    (center3571.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3571]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3571 : work3571.theta.ok = true ∧
    work3571.jac.invOK = true ∧ acceptsUnitSq work3571.out = true := by
  norm_num [work3571, contact3571, tau3571, center3571, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3571 : CellCertificate where
  tauBall := tau3571
  contactCenter := center3571
  contactBall := contact3571
  work := work3571
  center_sq := center_sq3571
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3571.1
  jac_ok := checks3571.2.1
  accepted := checks3571.2.2

def tau3572 : RatBall :=
  ⟨⟨21/640, 249/640⟩, 3/1280⟩
def center3572 : GaussianRat :=
  ⟨26958403/1000000000, 284882077/1000000000⟩
def contact3572 : RatBall := localContactBall tau3572 center3572
def work3572 : RoundedTauEval :=
  evalTau precision tau3572 contact3572 logTwoBall

theorem center_sq3572 : (center3572.re : ℝ)^2 +
    (center3572.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3572]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3572 : work3572.theta.ok = true ∧
    work3572.jac.invOK = true ∧ acceptsUnitSq work3572.out = true := by
  norm_num [work3572, contact3572, tau3572, center3572, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3572 : CellCertificate where
  tauBall := tau3572
  contactCenter := center3572
  contactBall := contact3572
  work := work3572
  center_sq := center_sq3572
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3572.1
  jac_ok := checks3572.2.1
  accepted := checks3572.2.2

def tau3573 : RatBall :=
  ⟨⟨23/640, 249/640⟩, 3/1280⟩
def center3573 : GaussianRat :=
  ⟨29521383/1000000000, 142399033/500000000⟩
def contact3573 : RatBall := localContactBall tau3573 center3573
def work3573 : RoundedTauEval :=
  evalTau precision tau3573 contact3573 logTwoBall

theorem center_sq3573 : (center3573.re : ℝ)^2 +
    (center3573.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3573]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3573 : work3573.theta.ok = true ∧
    work3573.jac.invOK = true ∧ acceptsUnitSq work3573.out = true := by
  norm_num [work3573, contact3573, tau3573, center3573, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3573 : CellCertificate where
  tauBall := tau3573
  contactCenter := center3573
  contactBall := contact3573
  work := work3573
  center_sq := center_sq3573
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3573.1
  jac_ok := checks3573.2.1
  accepted := checks3573.2.2

def tau3574 : RatBall :=
  ⟨⟨21/640, 251/640⟩, 3/1280⟩
def center3574 : GaussianRat :=
  ⟨1689949/62500000, 143724721/500000000⟩
def contact3574 : RatBall := localContactBall tau3574 center3574
def work3574 : RoundedTauEval :=
  evalTau precision tau3574 contact3574 logTwoBall

theorem center_sq3574 : (center3574.re : ℝ)^2 +
    (center3574.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3574]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3574 : work3574.theta.ok = true ∧
    work3574.jac.invOK = true ∧ acceptsUnitSq work3574.out = true := by
  norm_num [work3574, contact3574, tau3574, center3574, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3574 : CellCertificate where
  tauBall := tau3574
  contactCenter := center3574
  contactBall := contact3574
  work := work3574
  center_sq := center_sq3574
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3574.1
  jac_ok := checks3574.2.1
  accepted := checks3574.2.2

def tau3575 : RatBall :=
  ⟨⟨23/640, 251/640⟩, 3/1280⟩
def center3575 : GaussianRat :=
  ⟨14804897/500000000, 8980133/31250000⟩
def contact3575 : RatBall := localContactBall tau3575 center3575
def work3575 : RoundedTauEval :=
  evalTau precision tau3575 contact3575 logTwoBall

theorem center_sq3575 : (center3575.re : ℝ)^2 +
    (center3575.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3575]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3575 : work3575.theta.ok = true ∧
    work3575.jac.invOK = true ∧ acceptsUnitSq work3575.out = true := by
  norm_num [work3575, contact3575, tau3575, center3575, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3575 : CellCertificate where
  tauBall := tau3575
  contactCenter := center3575
  contactBall := contact3575
  work := work3575
  center_sq := center_sq3575
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3575.1
  jac_ok := checks3575.2.1
  accepted := checks3575.2.2

def cells : List CellCertificate := [cell3568, cell3569, cell3570, cell3571, cell3572, cell3573, cell3574, cell3575]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446
