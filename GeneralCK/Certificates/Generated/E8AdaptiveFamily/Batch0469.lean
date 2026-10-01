import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3752 : RatBall :=
  ⟨⟨71/640, 241/640⟩, 3/1280⟩
def center3752 : GaussianRat :=
  ⟨89415553/1000000000, 270605413/1000000000⟩
def contact3752 : RatBall := localContactBall tau3752 center3752
def work3752 : RoundedTauEval :=
  evalTau precision tau3752 contact3752 logTwoBall

theorem center_sq3752 : (center3752.re : ℝ)^2 +
    (center3752.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3752]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3752 : work3752.theta.ok = true ∧
    work3752.jac.invOK = true ∧ acceptsUnitSq work3752.out = true := by
  norm_num [work3752, contact3752, tau3752, center3752, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3752 : CellCertificate where
  tauBall := tau3752
  contactCenter := center3752
  contactBall := contact3752
  work := work3752
  center_sq := center_sq3752
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3752.1
  jac_ok := checks3752.2.1
  accepted := checks3752.2.2

def tau3753 : RatBall :=
  ⟨⟨69/640, 243/640⟩, 3/1280⟩
def center3753 : GaussianRat :=
  ⟨87178851/1000000000, 273334167/1000000000⟩
def contact3753 : RatBall := localContactBall tau3753 center3753
def work3753 : RoundedTauEval :=
  evalTau precision tau3753 contact3753 logTwoBall

theorem center_sq3753 : (center3753.re : ℝ)^2 +
    (center3753.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3753]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3753 : work3753.theta.ok = true ∧
    work3753.jac.invOK = true ∧ acceptsUnitSq work3753.out = true := by
  norm_num [work3753, contact3753, tau3753, center3753, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3753 : CellCertificate where
  tauBall := tau3753
  contactCenter := center3753
  contactBall := contact3753
  work := work3753
  center_sq := center_sq3753
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3753.1
  jac_ok := checks3753.2.1
  accepted := checks3753.2.2

def tau3754 : RatBall :=
  ⟨⟨71/640, 243/640⟩, 3/1280⟩
def center3754 : GaussianRat :=
  ⟨89664833/1000000000, 68271613/250000000⟩
def contact3754 : RatBall := localContactBall tau3754 center3754
def work3754 : RoundedTauEval :=
  evalTau precision tau3754 contact3754 logTwoBall

theorem center_sq3754 : (center3754.re : ℝ)^2 +
    (center3754.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3754]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3754 : work3754.theta.ok = true ∧
    work3754.jac.invOK = true ∧ acceptsUnitSq work3754.out = true := by
  norm_num [work3754, contact3754, tau3754, center3754, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3754 : CellCertificate where
  tauBall := tau3754
  contactCenter := center3754
  contactBall := contact3754
  work := work3754
  center_sq := center_sq3754
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3754.1
  jac_ok := checks3754.2.1
  accepted := checks3754.2.2

def tau3755 : RatBall :=
  ⟨⟨13/128, 49/128⟩, 3/1280⟩
def center3755 : GaussianRat :=
  ⟨41214889/500000000, 1726921/6250000⟩
def contact3755 : RatBall := localContactBall tau3755 center3755
def work3755 : RoundedTauEval :=
  evalTau precision tau3755 contact3755 logTwoBall

theorem center_sq3755 : (center3755.re : ℝ)^2 +
    (center3755.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3755]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3755 : work3755.theta.ok = true ∧
    work3755.jac.invOK = true ∧ acceptsUnitSq work3755.out = true := by
  norm_num [work3755, contact3755, tau3755, center3755, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3755 : CellCertificate where
  tauBall := tau3755
  contactCenter := center3755
  contactBall := contact3755
  work := work3755
  center_sq := center_sq3755
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3755.1
  jac_ok := checks3755.2.1
  accepted := checks3755.2.2

def tau3756 : RatBall :=
  ⟨⟨67/640, 49/128⟩, 3/1280⟩
def center3756 : GaussianRat :=
  ⟨42464509/500000000, 34508699/125000000⟩
def contact3756 : RatBall := localContactBall tau3756 center3756
def work3756 : RoundedTauEval :=
  evalTau precision tau3756 contact3756 logTwoBall

theorem center_sq3756 : (center3756.re : ℝ)^2 +
    (center3756.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3756]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3756 : work3756.theta.ok = true ∧
    work3756.jac.invOK = true ∧ acceptsUnitSq work3756.out = true := by
  norm_num [work3756, contact3756, tau3756, center3756, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3756 : CellCertificate where
  tauBall := tau3756
  contactCenter := center3756
  contactBall := contact3756
  work := work3756
  center_sq := center_sq3756
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3756.1
  jac_ok := checks3756.2.1
  accepted := checks3756.2.2

def tau3757 : RatBall :=
  ⟨⟨13/128, 247/640⟩, 3/1280⟩
def center3757 : GaussianRat :=
  ⟨82665793/1000000000, 278811601/1000000000⟩
def contact3757 : RatBall := localContactBall tau3757 center3757
def work3757 : RoundedTauEval :=
  evalTau precision tau3757 contact3757 logTwoBall

theorem center_sq3757 : (center3757.re : ℝ)^2 +
    (center3757.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3757]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3757 : work3757.theta.ok = true ∧
    work3757.jac.invOK = true ∧ acceptsUnitSq work3757.out = true := by
  norm_num [work3757, contact3757, tau3757, center3757, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3757 : CellCertificate where
  tauBall := tau3757
  contactCenter := center3757
  contactBall := contact3757
  work := work3757
  center_sq := center_sq3757
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3757.1
  jac_ok := checks3757.2.1
  accepted := checks3757.2.2

def tau3758 : RatBall :=
  ⟨⟨67/640, 247/640⟩, 3/1280⟩
def center3758 : GaussianRat :=
  ⟨42585897/500000000, 278570563/1000000000⟩
def contact3758 : RatBall := localContactBall tau3758 center3758
def work3758 : RoundedTauEval :=
  evalTau precision tau3758 contact3758 logTwoBall

theorem center_sq3758 : (center3758.re : ℝ)^2 +
    (center3758.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3758]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3758 : work3758.theta.ok = true ∧
    work3758.jac.invOK = true ∧ acceptsUnitSq work3758.out = true := by
  norm_num [work3758, contact3758, tau3758, center3758, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3758 : CellCertificate where
  tauBall := tau3758
  contactCenter := center3758
  contactBall := contact3758
  work := work3758
  center_sq := center_sq3758
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3758.1
  jac_ok := checks3758.2.1
  accepted := checks3758.2.2

def tau3759 : RatBall :=
  ⟨⟨69/640, 49/128⟩, 3/1280⟩
def center3759 : GaussianRat :=
  ⟨43712483/500000000, 34478141/125000000⟩
def contact3759 : RatBall := localContactBall tau3759 center3759
def work3759 : RoundedTauEval :=
  evalTau precision tau3759 contact3759 logTwoBall

theorem center_sq3759 : (center3759.re : ℝ)^2 +
    (center3759.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3759]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3759 : work3759.theta.ok = true ∧
    work3759.jac.invOK = true ∧ acceptsUnitSq work3759.out = true := by
  norm_num [work3759, contact3759, tau3759, center3759, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3759 : CellCertificate where
  tauBall := tau3759
  contactCenter := center3759
  contactBall := contact3759
  work := work3759
  center_sq := center_sq3759
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3759.1
  jac_ok := checks3759.2.1
  accepted := checks3759.2.2

def cells : List CellCertificate := [cell3752, cell3753, cell3754, cell3755, cell3756, cell3757, cell3758, cell3759]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469
