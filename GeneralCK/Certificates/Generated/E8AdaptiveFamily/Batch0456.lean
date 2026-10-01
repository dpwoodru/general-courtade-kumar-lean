import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3648 : RatBall :=
  ⟨⟨11/128, 241/640⟩, 3/1280⟩
def center3648 : GaussianRat :=
  ⟨34746169/500000000, 68094139/250000000⟩
def contact3648 : RatBall := localContactBall tau3648 center3648
def work3648 : RoundedTauEval :=
  evalTau precision tau3648 contact3648 logTwoBall

theorem center_sq3648 : (center3648.re : ℝ)^2 +
    (center3648.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3648]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3648 : work3648.theta.ok = true ∧
    work3648.jac.invOK = true ∧ acceptsUnitSq work3648.out = true := by
  norm_num [work3648, contact3648, tau3648, center3648, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3648 : CellCertificate where
  tauBall := tau3648
  contactCenter := center3648
  contactBall := contact3648
  work := work3648
  center_sq := center_sq3648
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3648.1
  jac_ok := checks3648.2.1
  accepted := checks3648.2.2

def tau3649 : RatBall :=
  ⟨⟨53/640, 243/640⟩, 3/1280⟩
def center3649 : GaussianRat :=
  ⟨67178257/1000000000, 137538033/500000000⟩
def contact3649 : RatBall := localContactBall tau3649 center3649
def work3649 : RoundedTauEval :=
  evalTau precision tau3649 contact3649 logTwoBall

theorem center_sq3649 : (center3649.re : ℝ)^2 +
    (center3649.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3649]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3649 : work3649.theta.ok = true ∧
    work3649.jac.invOK = true ∧ acceptsUnitSq work3649.out = true := by
  norm_num [work3649, contact3649, tau3649, center3649, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3649 : CellCertificate where
  tauBall := tau3649
  contactCenter := center3649
  contactBall := contact3649
  work := work3649
  center_sq := center_sq3649
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3649.1
  jac_ok := checks3649.2.1
  accepted := checks3649.2.2

def tau3650 : RatBall :=
  ⟨⟨11/128, 243/640⟩, 3/1280⟩
def center3650 : GaussianRat :=
  ⟨13937693/200000000, 54976403/200000000⟩
def contact3650 : RatBall := localContactBall tau3650 center3650
def work3650 : RoundedTauEval :=
  evalTau precision tau3650 contact3650 logTwoBall

theorem center_sq3650 : (center3650.re : ℝ)^2 +
    (center3650.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3650]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3650 : work3650.theta.ok = true ∧
    work3650.jac.invOK = true ∧ acceptsUnitSq work3650.out = true := by
  norm_num [work3650, contact3650, tau3650, center3650, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3650 : CellCertificate where
  tauBall := tau3650
  contactCenter := center3650
  contactBall := contact3650
  work := work3650
  center_sq := center_sq3650
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3650.1
  jac_ok := checks3650.2.1
  accepted := checks3650.2.2

def tau3651 : RatBall :=
  ⟨⟨49/640, 49/128⟩, 3/1280⟩
def center3651 : GaussianRat :=
  ⟨31164041/500000000, 277963583/1000000000⟩
def contact3651 : RatBall := localContactBall tau3651 center3651
def work3651 : RoundedTauEval :=
  evalTau precision tau3651 contact3651 logTwoBall

theorem center_sq3651 : (center3651.re : ℝ)^2 +
    (center3651.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3651]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3651 : work3651.theta.ok = true ∧
    work3651.jac.invOK = true ∧ acceptsUnitSq work3651.out = true := by
  norm_num [work3651, contact3651, tau3651, center3651, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3651 : CellCertificate where
  tauBall := tau3651
  contactCenter := center3651
  contactBall := contact3651
  work := work3651
  center_sq := center_sq3651
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3651.1
  jac_ok := checks3651.2.1
  accepted := checks3651.2.2

def tau3652 : RatBall :=
  ⟨⟨51/640, 49/128⟩, 3/1280⟩
def center3652 : GaussianRat :=
  ⟨3242521/50000000, 138890411/500000000⟩
def contact3652 : RatBall := localContactBall tau3652 center3652
def work3652 : RoundedTauEval :=
  evalTau precision tau3652 contact3652 logTwoBall

theorem center_sq3652 : (center3652.re : ℝ)^2 +
    (center3652.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3652]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3652 : work3652.theta.ok = true ∧
    work3652.jac.invOK = true ∧ acceptsUnitSq work3652.out = true := by
  norm_num [work3652, contact3652, tau3652, center3652, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3652 : CellCertificate where
  tauBall := tau3652
  contactCenter := center3652
  contactBall := contact3652
  work := work3652
  center_sq := center_sq3652
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3652.1
  jac_ok := checks3652.2.1
  accepted := checks3652.2.2

def tau3653 : RatBall :=
  ⟨⟨49/640, 247/640⟩, 3/1280⟩
def center3653 : GaussianRat :=
  ⟨6250857/100000000, 280490707/1000000000⟩
def contact3653 : RatBall := localContactBall tau3653 center3653
def work3653 : RoundedTauEval :=
  evalTau precision tau3653 contact3653 logTwoBall

theorem center_sq3653 : (center3653.re : ℝ)^2 +
    (center3653.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3653]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3653 : work3653.theta.ok = true ∧
    work3653.jac.invOK = true ∧ acceptsUnitSq work3653.out = true := by
  norm_num [work3653, contact3653, tau3653, center3653, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3653 : CellCertificate where
  tauBall := tau3653
  contactCenter := center3653
  contactBall := contact3653
  work := work3653
  center_sq := center_sq3653
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3653.1
  jac_ok := checks3653.2.1
  accepted := checks3653.2.2

def tau3654 : RatBall :=
  ⟨⟨51/640, 247/640⟩, 3/1280⟩
def center3654 : GaussianRat :=
  ⟨32518989/500000000, 70076353/250000000⟩
def contact3654 : RatBall := localContactBall tau3654 center3654
def work3654 : RoundedTauEval :=
  evalTau precision tau3654 contact3654 logTwoBall

theorem center_sq3654 : (center3654.re : ℝ)^2 +
    (center3654.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3654]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3654 : work3654.theta.ok = true ∧
    work3654.jac.invOK = true ∧ acceptsUnitSq work3654.out = true := by
  norm_num [work3654, contact3654, tau3654, center3654, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3654 : CellCertificate where
  tauBall := tau3654
  contactCenter := center3654
  contactBall := contact3654
  work := work3654
  center_sq := center_sq3654
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3654.1
  jac_ok := checks3654.2.1
  accepted := checks3654.2.2

def tau3655 : RatBall :=
  ⟨⟨53/640, 49/128⟩, 3/1280⟩
def center3655 : GaussianRat :=
  ⟨4210637/62500000, 55518211/200000000⟩
def contact3655 : RatBall := localContactBall tau3655 center3655
def work3655 : RoundedTauEval :=
  evalTau precision tau3655 contact3655 logTwoBall

theorem center_sq3655 : (center3655.re : ℝ)^2 +
    (center3655.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3655]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3655 : work3655.theta.ok = true ∧
    work3655.jac.invOK = true ∧ acceptsUnitSq work3655.out = true := by
  norm_num [work3655, contact3655, tau3655, center3655, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3655 : CellCertificate where
  tauBall := tau3655
  contactCenter := center3655
  contactBall := contact3655
  work := work3655
  center_sq := center_sq3655
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3655.1
  jac_ok := checks3655.2.1
  accepted := checks3655.2.2

def cells : List CellCertificate := [cell3648, cell3649, cell3650, cell3651, cell3652, cell3653, cell3654, cell3655]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456
