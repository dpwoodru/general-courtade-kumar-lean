import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3680 : RatBall :=
  ⟨⟨11/128, 249/640⟩, 3/1280⟩
def center3680 : GaussianRat :=
  ⟨70293283/1000000000, 14121991/50000000⟩
def contact3680 : RatBall := localContactBall tau3680 center3680
def work3680 : RoundedTauEval :=
  evalTau precision tau3680 contact3680 logTwoBall

theorem center_sq3680 : (center3680.re : ℝ)^2 +
    (center3680.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3680]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3680 : work3680.theta.ok = true ∧
    work3680.jac.invOK = true ∧ acceptsUnitSq work3680.out = true := by
  norm_num [work3680, contact3680, tau3680, center3680, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3680 : CellCertificate where
  tauBall := tau3680
  contactCenter := center3680
  contactBall := contact3680
  work := work3680
  center_sq := center_sq3680
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3680.1
  jac_ok := checks3680.2.1
  accepted := checks3680.2.2

def tau3681 : RatBall :=
  ⟨⟨53/640, 251/640⟩, 3/1280⟩
def center3681 : GaussianRat :=
  ⟨67962093/1000000000, 285178227/1000000000⟩
def contact3681 : RatBall := localContactBall tau3681 center3681
def work3681 : RoundedTauEval :=
  evalTau precision tau3681 contact3681 logTwoBall

theorem center_sq3681 : (center3681.re : ℝ)^2 +
    (center3681.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3681]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3681 : work3681.theta.ok = true ∧
    work3681.jac.invOK = true ∧ acceptsUnitSq work3681.out = true := by
  norm_num [work3681, contact3681, tau3681, center3681, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3681 : CellCertificate where
  tauBall := tau3681
  contactCenter := center3681
  contactBall := contact3681
  work := work3681
  center_sq := center_sq3681
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3681.1
  jac_ok := checks3681.2.1
  accepted := checks3681.2.2

def tau3682 : RatBall :=
  ⟨⟨11/128, 251/640⟩, 3/1280⟩
def center3682 : GaussianRat :=
  ⟨70500491/1000000000, 35621651/125000000⟩
def contact3682 : RatBall := localContactBall tau3682 center3682
def work3682 : RoundedTauEval :=
  evalTau precision tau3682 contact3682 logTwoBall

theorem center_sq3682 : (center3682.re : ℝ)^2 +
    (center3682.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3682]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3682 : work3682.theta.ok = true ∧
    work3682.jac.invOK = true ∧ acceptsUnitSq work3682.out = true := by
  norm_num [work3682, contact3682, tau3682, center3682, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3682 : CellCertificate where
  tauBall := tau3682
  contactCenter := center3682
  contactBall := contact3682
  work := work3682
  center_sq := center_sq3682
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3682.1
  jac_ok := checks3682.2.1
  accepted := checks3682.2.2

def tau3683 : RatBall :=
  ⟨⟨57/640, 249/640⟩, 3/1280⟩
def center3683 : GaussianRat :=
  ⟨14564333/200000000, 70557619/250000000⟩
def contact3683 : RatBall := localContactBall tau3683 center3683
def work3683 : RoundedTauEval :=
  evalTau precision tau3683 contact3683 logTwoBall

theorem center_sq3683 : (center3683.re : ℝ)^2 +
    (center3683.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3683]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3683 : work3683.theta.ok = true ∧
    work3683.jac.invOK = true ∧ acceptsUnitSq work3683.out = true := by
  norm_num [work3683, contact3683, tau3683, center3683, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3683 : CellCertificate where
  tauBall := tau3683
  contactCenter := center3683
  contactBall := contact3683
  work := work3683
  center_sq := center_sq3683
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3683.1
  jac_ok := checks3683.2.1
  accepted := checks3683.2.2

def tau3684 : RatBall :=
  ⟨⟨59/640, 249/640⟩, 3/1280⟩
def center3684 : GaussianRat :=
  ⟨75347127/1000000000, 8812939/31250000⟩
def contact3684 : RatBall := localContactBall tau3684 center3684
def work3684 : RoundedTauEval :=
  evalTau precision tau3684 contact3684 logTwoBall

theorem center_sq3684 : (center3684.re : ℝ)^2 +
    (center3684.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3684]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3684 : work3684.theta.ok = true ∧
    work3684.jac.invOK = true ∧ acceptsUnitSq work3684.out = true := by
  norm_num [work3684, contact3684, tau3684, center3684, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3684 : CellCertificate where
  tauBall := tau3684
  contactCenter := center3684
  contactBall := contact3684
  work := work3684
  center_sq := center_sq3684
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3684.1
  jac_ok := checks3684.2.1
  accepted := checks3684.2.2

def tau3685 : RatBall :=
  ⟨⟨61/640, 249/640⟩, 3/1280⟩
def center3685 : GaussianRat :=
  ⟨38934787/500000000, 281790577/1000000000⟩
def contact3685 : RatBall := localContactBall tau3685 center3685
def work3685 : RoundedTauEval :=
  evalTau precision tau3685 contact3685 logTwoBall

theorem center_sq3685 : (center3685.re : ℝ)^2 +
    (center3685.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3685]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3685 : work3685.theta.ok = true ∧
    work3685.jac.invOK = true ∧ acceptsUnitSq work3685.out = true := by
  norm_num [work3685, contact3685, tau3685, center3685, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3685 : CellCertificate where
  tauBall := tau3685
  contactCenter := center3685
  contactBall := contact3685
  work := work3685
  center_sq := center_sq3685
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3685.1
  jac_ok := checks3685.2.1
  accepted := checks3685.2.2

def tau3686 : RatBall :=
  ⟨⟨63/640, 249/640⟩, 3/1280⟩
def center3686 : GaussianRat :=
  ⟨16077783/200000000, 281560103/1000000000⟩
def contact3686 : RatBall := localContactBall tau3686 center3686
def work3686 : RoundedTauEval :=
  evalTau precision tau3686 contact3686 logTwoBall

theorem center_sq3686 : (center3686.re : ℝ)^2 +
    (center3686.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3686]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3686 : work3686.theta.ok = true ∧
    work3686.jac.invOK = true ∧ acceptsUnitSq work3686.out = true := by
  norm_num [work3686, contact3686, tau3686, center3686, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3686 : CellCertificate where
  tauBall := tau3686
  contactCenter := center3686
  contactBall := contact3686
  work := work3686
  center_sq := center_sq3686
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3686.1
  jac_ok := checks3686.2.1
  accepted := checks3686.2.2

def tau3687 : RatBall :=
  ⟨⟨121/640, 221/640⟩, 3/1280⟩
def center3687 : GaussianRat :=
  ⟨146422507/1000000000, 9563167/40000000⟩
def contact3687 : RatBall := localContactBall tau3687 center3687
def work3687 : RoundedTauEval :=
  evalTau precision tau3687 contact3687 logTwoBall

theorem center_sq3687 : (center3687.re : ℝ)^2 +
    (center3687.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3687]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3687 : work3687.theta.ok = true ∧
    work3687.jac.invOK = true ∧ acceptsUnitSq work3687.out = true := by
  norm_num [work3687, contact3687, tau3687, center3687, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3687 : CellCertificate where
  tauBall := tau3687
  contactCenter := center3687
  contactBall := contact3687
  work := work3687
  center_sq := center_sq3687
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3687.1
  jac_ok := checks3687.2.1
  accepted := checks3687.2.2

def cells : List CellCertificate := [cell3680, cell3681, cell3682, cell3683, cell3684, cell3685, cell3686, cell3687]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460
