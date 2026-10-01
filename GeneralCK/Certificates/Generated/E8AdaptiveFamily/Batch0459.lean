import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3672 : RatBall :=
  ⟨⟨63/640, 49/128⟩, 3/1280⟩
def center3672 : GaussianRat :=
  ⟨39963667/500000000, 276538391/1000000000⟩
def contact3672 : RatBall := localContactBall tau3672 center3672
def work3672 : RoundedTauEval :=
  evalTau precision tau3672 contact3672 logTwoBall

theorem center_sq3672 : (center3672.re : ℝ)^2 +
    (center3672.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3672]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3672 : work3672.theta.ok = true ∧
    work3672.jac.invOK = true ∧ acceptsUnitSq work3672.out = true := by
  norm_num [work3672, contact3672, tau3672, center3672, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3672 : CellCertificate where
  tauBall := tau3672
  contactCenter := center3672
  contactBall := contact3672
  work := work3672
  center_sq := center_sq3672
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3672.1
  jac_ok := checks3672.2.1
  accepted := checks3672.2.2

def tau3673 : RatBall :=
  ⟨⟨61/640, 247/640⟩, 3/1280⟩
def center3673 : GaussianRat :=
  ⟨77644141/1000000000, 139636577/500000000⟩
def contact3673 : RatBall := localContactBall tau3673 center3673
def work3673 : RoundedTauEval :=
  evalTau precision tau3673 contact3673 logTwoBall

theorem center_sq3673 : (center3673.re : ℝ)^2 +
    (center3673.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3673]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3673 : work3673.theta.ok = true ∧
    work3673.jac.invOK = true ∧ acceptsUnitSq work3673.out = true := by
  norm_num [work3673, contact3673, tau3673, center3673, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3673 : CellCertificate where
  tauBall := tau3673
  contactCenter := center3673
  contactBall := contact3673
  work := work3673
  center_sq := center_sq3673
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3673.1
  jac_ok := checks3673.2.1
  accepted := checks3673.2.2

def tau3674 : RatBall :=
  ⟨⟨63/640, 247/640⟩, 3/1280⟩
def center3674 : GaussianRat :=
  ⟨40078273/500000000, 69761453/250000000⟩
def contact3674 : RatBall := localContactBall tau3674 center3674
def work3674 : RoundedTauEval :=
  evalTau precision tau3674 contact3674 logTwoBall

theorem center_sq3674 : (center3674.re : ℝ)^2 +
    (center3674.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3674]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3674 : work3674.theta.ok = true ∧
    work3674.jac.invOK = true ∧ acceptsUnitSq work3674.out = true := by
  norm_num [work3674, contact3674, tau3674, center3674, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3674 : CellCertificate where
  tauBall := tau3674
  contactCenter := center3674
  contactBall := contact3674
  work := work3674
  center_sq := center_sq3674
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3674.1
  jac_ok := checks3674.2.1
  accepted := checks3674.2.2

def tau3675 : RatBall :=
  ⟨⟨49/640, 249/640⟩, 3/1280⟩
def center3675 : GaussianRat :=
  ⟨62691561/1000000000, 141512483/500000000⟩
def contact3675 : RatBall := localContactBall tau3675 center3675
def work3675 : RoundedTauEval :=
  evalTau precision tau3675 contact3675 logTwoBall

theorem center_sq3675 : (center3675.re : ℝ)^2 +
    (center3675.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3675]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3675 : work3675.theta.ok = true ∧
    work3675.jac.invOK = true ∧ acceptsUnitSq work3675.out = true := by
  norm_num [work3675, contact3675, tau3675, center3675, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3675 : CellCertificate where
  tauBall := tau3675
  contactCenter := center3675
  contactBall := contact3675
  work := work3675
  center_sq := center_sq3675
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3675.1
  jac_ok := checks3675.2.1
  accepted := checks3675.2.2

def tau3676 : RatBall :=
  ⟨⟨51/640, 249/640⟩, 3/1280⟩
def center3676 : GaussianRat :=
  ⟨13045627/200000000, 141418551/500000000⟩
def contact3676 : RatBall := localContactBall tau3676 center3676
def work3676 : RoundedTauEval :=
  evalTau precision tau3676 contact3676 logTwoBall

theorem center_sq3676 : (center3676.re : ℝ)^2 +
    (center3676.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3676]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3676 : work3676.theta.ok = true ∧
    work3676.jac.invOK = true ∧ acceptsUnitSq work3676.out = true := by
  norm_num [work3676, contact3676, tau3676, center3676, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3676 : CellCertificate where
  tauBall := tau3676
  contactCenter := center3676
  contactBall := contact3676
  work := work3676
  center_sq := center_sq3676
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3676.1
  jac_ok := checks3676.2.1
  accepted := checks3676.2.2

def tau3677 : RatBall :=
  ⟨⟨49/640, 251/640⟩, 3/1280⟩
def center3677 : GaussianRat :=
  ⟨6287709/100000000, 142783229/500000000⟩
def contact3677 : RatBall := localContactBall tau3677 center3677
def work3677 : RoundedTauEval :=
  evalTau precision tau3677 contact3677 logTwoBall

theorem center_sq3677 : (center3677.re : ℝ)^2 +
    (center3677.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3677]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3677 : work3677.theta.ok = true ∧
    work3677.jac.invOK = true ∧ acceptsUnitSq work3677.out = true := by
  norm_num [work3677, contact3677, tau3677, center3677, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3677 : CellCertificate where
  tauBall := tau3677
  contactCenter := center3677
  contactBall := contact3677
  work := work3677
  center_sq := center_sq3677
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3677.1
  jac_ok := checks3677.2.1
  accepted := checks3677.2.2

def tau3678 : RatBall :=
  ⟨⟨51/640, 251/640⟩, 3/1280⟩
def center3678 : GaussianRat :=
  ⟨65420927/1000000000, 285375989/1000000000⟩
def contact3678 : RatBall := localContactBall tau3678 center3678
def work3678 : RoundedTauEval :=
  evalTau precision tau3678 contact3678 logTwoBall

theorem center_sq3678 : (center3678.re : ℝ)^2 +
    (center3678.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3678]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3678 : work3678.theta.ok = true ∧
    work3678.jac.invOK = true ∧ acceptsUnitSq work3678.out = true := by
  norm_num [work3678, contact3678, tau3678, center3678, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3678 : CellCertificate where
  tauBall := tau3678
  contactCenter := center3678
  contactBall := contact3678
  work := work3678
  center_sq := center_sq3678
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3678.1
  jac_ok := checks3678.2.1
  accepted := checks3678.2.2

def tau3679 : RatBall :=
  ⟨⟨53/640, 249/640⟩, 3/1280⟩
def center3679 : GaussianRat :=
  ⟨33881037/500000000, 282642041/1000000000⟩
def contact3679 : RatBall := localContactBall tau3679 center3679
def work3679 : RoundedTauEval :=
  evalTau precision tau3679 contact3679 logTwoBall

theorem center_sq3679 : (center3679.re : ℝ)^2 +
    (center3679.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3679]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3679 : work3679.theta.ok = true ∧
    work3679.jac.invOK = true ∧ acceptsUnitSq work3679.out = true := by
  norm_num [work3679, contact3679, tau3679, center3679, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3679 : CellCertificate where
  tauBall := tau3679
  contactCenter := center3679
  contactBall := contact3679
  work := work3679
  center_sq := center_sq3679
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3679.1
  jac_ok := checks3679.2.1
  accepted := checks3679.2.2

def cells : List CellCertificate := [cell3672, cell3673, cell3674, cell3675, cell3676, cell3677, cell3678, cell3679]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459
