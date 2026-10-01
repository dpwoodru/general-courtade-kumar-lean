import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3624 : RatBall :=
  ⟨⟨37/640, 249/640⟩, 3/1280⟩
def center3624 : GaussianRat :=
  ⟨11855567/250000000, 283999143/1000000000⟩
def contact3624 : RatBall := localContactBall tau3624 center3624
def work3624 : RoundedTauEval :=
  evalTau precision tau3624 contact3624 logTwoBall

theorem center_sq3624 : (center3624.re : ℝ)^2 +
    (center3624.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3624]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3624 : work3624.theta.ok = true ∧
    work3624.jac.invOK = true ∧ acceptsUnitSq work3624.out = true := by
  norm_num [work3624, contact3624, tau3624, center3624, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3624 : CellCertificate where
  tauBall := tau3624
  contactCenter := center3624
  contactBall := contact3624
  work := work3624
  center_sq := center_sq3624
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3624.1
  jac_ok := checks3624.2.1
  accepted := checks3624.2.2

def tau3625 : RatBall :=
  ⟨⟨39/640, 249/640⟩, 3/1280⟩
def center3625 : GaussianRat :=
  ⟨4997259/100000000, 17740947/62500000⟩
def contact3625 : RatBall := localContactBall tau3625 center3625
def work3625 : RoundedTauEval :=
  evalTau precision tau3625 contact3625 logTwoBall

theorem center_sq3625 : (center3625.re : ℝ)^2 +
    (center3625.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3625]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3625 : work3625.theta.ok = true ∧
    work3625.jac.invOK = true ∧ acceptsUnitSq work3625.out = true := by
  norm_num [work3625, contact3625, tau3625, center3625, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3625 : CellCertificate where
  tauBall := tau3625
  contactCenter := center3625
  contactBall := contact3625
  work := work3625
  center_sq := center_sq3625
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3625.1
  jac_ok := checks3625.2.1
  accepted := checks3625.2.2

def tau3626 : RatBall :=
  ⟨⟨37/640, 251/640⟩, 3/1280⟩
def center3626 : GaussianRat :=
  ⟨4756353/100000000, 4477409/15625000⟩
def contact3626 : RatBall := localContactBall tau3626 center3626
def work3626 : RoundedTauEval :=
  evalTau precision tau3626 contact3626 logTwoBall

theorem center_sq3626 : (center3626.re : ℝ)^2 +
    (center3626.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3626]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3626 : work3626.theta.ok = true ∧
    work3626.jac.invOK = true ∧ acceptsUnitSq work3626.out = true := by
  norm_num [work3626, contact3626, tau3626, center3626, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3626 : CellCertificate where
  tauBall := tau3626
  contactCenter := center3626
  contactBall := contact3626
  work := work3626
  center_sq := center_sq3626
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3626.1
  jac_ok := checks3626.2.1
  accepted := checks3626.2.2

def tau3627 : RatBall :=
  ⟨⟨39/640, 251/640⟩, 3/1280⟩
def center3627 : GaussianRat :=
  ⟨10024261/200000000, 14320409/50000000⟩
def contact3627 : RatBall := localContactBall tau3627 center3627
def work3627 : RoundedTauEval :=
  evalTau precision tau3627 contact3627 logTwoBall

theorem center_sq3627 : (center3627.re : ℝ)^2 +
    (center3627.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3627]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3627 : work3627.theta.ok = true ∧
    work3627.jac.invOK = true ∧ acceptsUnitSq work3627.out = true := by
  norm_num [work3627, contact3627, tau3627, center3627, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3627 : CellCertificate where
  tauBall := tau3627
  contactCenter := center3627
  contactBall := contact3627
  work := work3627
  center_sq := center_sq3627
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3627.1
  jac_ok := checks3627.2.1
  accepted := checks3627.2.2

def tau3628 : RatBall :=
  ⟨⟨33/640, 253/640⟩, 3/1280⟩
def center3628 : GaussianRat :=
  ⟨42570217/1000000000, 144694949/500000000⟩
def contact3628 : RatBall := localContactBall tau3628 center3628
def work3628 : RoundedTauEval :=
  evalTau precision tau3628 contact3628 logTwoBall

theorem center_sq3628 : (center3628.re : ℝ)^2 +
    (center3628.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3628]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3628 : work3628.theta.ok = true ∧
    work3628.jac.invOK = true ∧ acceptsUnitSq work3628.out = true := by
  norm_num [work3628, contact3628, tau3628, center3628, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3628 : CellCertificate where
  tauBall := tau3628
  contactCenter := center3628
  contactBall := contact3628
  work := work3628
  center_sq := center_sq3628
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3628.1
  jac_ok := checks3628.2.1
  accepted := checks3628.2.2

def tau3629 : RatBall :=
  ⟨⟨7/128, 253/640⟩, 3/1280⟩
def center3629 : GaussianRat :=
  ⟨9027887/200000000, 289257137/1000000000⟩
def contact3629 : RatBall := localContactBall tau3629 center3629
def work3629 : RoundedTauEval :=
  evalTau precision tau3629 contact3629 logTwoBall

theorem center_sq3629 : (center3629.re : ℝ)^2 +
    (center3629.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3629]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3629 : work3629.theta.ok = true ∧
    work3629.jac.invOK = true ∧ acceptsUnitSq work3629.out = true := by
  norm_num [work3629, contact3629, tau3629, center3629, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3629 : CellCertificate where
  tauBall := tau3629
  contactCenter := center3629
  contactBall := contact3629
  work := work3629
  center_sq := center_sq3629
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3629.1
  jac_ok := checks3629.2.1
  accepted := checks3629.2.2

def tau3630 : RatBall :=
  ⟨⟨37/640, 253/640⟩, 3/1280⟩
def center3630 : GaussianRat :=
  ⟨47706761/1000000000, 36139591/125000000⟩
def contact3630 : RatBall := localContactBall tau3630 center3630
def work3630 : RoundedTauEval :=
  evalTau precision tau3630 contact3630 logTwoBall

theorem center_sq3630 : (center3630.re : ℝ)^2 +
    (center3630.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3630]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3630 : work3630.theta.ok = true ∧
    work3630.jac.invOK = true ∧ acceptsUnitSq work3630.out = true := by
  norm_num [work3630, contact3630, tau3630, center3630, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3630 : CellCertificate where
  tauBall := tau3630
  contactCenter := center3630
  contactBall := contact3630
  work := work3630
  center_sq := center_sq3630
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3630.1
  jac_ok := checks3630.2.1
  accepted := checks3630.2.2

def tau3631 : RatBall :=
  ⟨⟨39/640, 253/640⟩, 3/1280⟩
def center3631 : GaussianRat :=
  ⟨50272091/1000000000, 144484349/500000000⟩
def contact3631 : RatBall := localContactBall tau3631 center3631
def work3631 : RoundedTauEval :=
  evalTau precision tau3631 contact3631 logTwoBall

theorem center_sq3631 : (center3631.re : ℝ)^2 +
    (center3631.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3631]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3631 : work3631.theta.ok = true ∧
    work3631.jac.invOK = true ∧ acceptsUnitSq work3631.out = true := by
  norm_num [work3631, contact3631, tau3631, center3631, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3631 : CellCertificate where
  tauBall := tau3631
  contactCenter := center3631
  contactBall := contact3631
  work := work3631
  center_sq := center_sq3631
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3631.1
  jac_ok := checks3631.2.1
  accepted := checks3631.2.2

def cells : List CellCertificate := [cell3624, cell3625, cell3626, cell3627, cell3628, cell3629, cell3630, cell3631]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453
