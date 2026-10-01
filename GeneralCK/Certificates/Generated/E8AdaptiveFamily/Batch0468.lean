import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3744 : RatBall :=
  ⟨⟨19/128, 237/640⟩, 3/1280⟩
def center3744 : GaussianRat :=
  ⟨29562099/250000000, 262332709/1000000000⟩
def contact3744 : RatBall := localContactBall tau3744 center3744
def work3744 : RoundedTauEval :=
  evalTau precision tau3744 contact3744 logTwoBall

theorem center_sq3744 : (center3744.re : ℝ)^2 +
    (center3744.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3744]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3744 : work3744.theta.ok = true ∧
    work3744.jac.invOK = true ∧ acceptsUnitSq work3744.out = true := by
  norm_num [work3744, contact3744, tau3744, center3744, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3744 : CellCertificate where
  tauBall := tau3744
  contactCenter := center3744
  contactBall := contact3744
  work := work3744
  center_sq := center_sq3744
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3744.1
  jac_ok := checks3744.2.1
  accepted := checks3744.2.2

def tau3745 : RatBall :=
  ⟨⟨93/640, 239/640⟩, 3/1280⟩
def center3745 : GaussianRat :=
  ⟨116135629/1000000000, 265069807/1000000000⟩
def contact3745 : RatBall := localContactBall tau3745 center3745
def work3745 : RoundedTauEval :=
  evalTau precision tau3745 contact3745 logTwoBall

theorem center_sq3745 : (center3745.re : ℝ)^2 +
    (center3745.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3745]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3745 : work3745.theta.ok = true ∧
    work3745.jac.invOK = true ∧ acceptsUnitSq work3745.out = true := by
  norm_num [work3745, contact3745, tau3745, center3745, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3745 : CellCertificate where
  tauBall := tau3745
  contactCenter := center3745
  contactBall := contact3745
  work := work3745
  center_sq := center_sq3745
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3745.1
  jac_ok := checks3745.2.1
  accepted := checks3745.2.2

def tau3746 : RatBall :=
  ⟨⟨19/128, 239/640⟩, 3/1280⟩
def center3746 : GaussianRat :=
  ⟨118563451/1000000000, 66188883/250000000⟩
def contact3746 : RatBall := localContactBall tau3746 center3746
def work3746 : RoundedTauEval :=
  evalTau precision tau3746 contact3746 logTwoBall

theorem center_sq3746 : (center3746.re : ℝ)^2 +
    (center3746.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3746]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3746 : work3746.theta.ok = true ∧
    work3746.jac.invOK = true ∧ acceptsUnitSq work3746.out = true := by
  norm_num [work3746, contact3746, tau3746, center3746, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3746 : CellCertificate where
  tauBall := tau3746
  contactCenter := center3746
  contactBall := contact3746
  work := work3746
  center_sq := center_sq3746
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3746.1
  jac_ok := checks3746.2.1
  accepted := checks3746.2.2

def tau3747 : RatBall :=
  ⟨⟨13/128, 241/640⟩, 3/1280⟩
def center3747 : GaussianRat :=
  ⟨40983659/500000000, 135659503/500000000⟩
def contact3747 : RatBall := localContactBall tau3747 center3747
def work3747 : RoundedTauEval :=
  evalTau precision tau3747 contact3747 logTwoBall

theorem center_sq3747 : (center3747.re : ℝ)^2 +
    (center3747.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3747]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3747 : work3747.theta.ok = true ∧
    work3747.jac.invOK = true ∧ acceptsUnitSq work3747.out = true := by
  norm_num [work3747, contact3747, tau3747, center3747, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3747 : CellCertificate where
  tauBall := tau3747
  contactCenter := center3747
  contactBall := contact3747
  work := work3747
  center_sq := center_sq3747
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3747.1
  jac_ok := checks3747.2.1
  accepted := checks3747.2.2

def tau3748 : RatBall :=
  ⟨⟨67/640, 241/640⟩, 3/1280⟩
def center3748 : GaussianRat :=
  ⟨84453299/1000000000, 5421753/20000000⟩
def contact3748 : RatBall := localContactBall tau3748 center3748
def work3748 : RoundedTauEval :=
  evalTau precision tau3748 contact3748 logTwoBall

theorem center_sq3748 : (center3748.re : ℝ)^2 +
    (center3748.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3748]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3748 : work3748.theta.ok = true ∧
    work3748.jac.invOK = true ∧ acceptsUnitSq work3748.out = true := by
  norm_num [work3748, contact3748, tau3748, center3748, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3748 : CellCertificate where
  tauBall := tau3748
  contactCenter := center3748
  contactBall := contact3748
  work := work3748
  center_sq := center_sq3748
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3748.1
  jac_ok := checks3748.2.1
  accepted := checks3748.2.2

def tau3749 : RatBall :=
  ⟨⟨13/128, 243/640⟩, 3/1280⟩
def center3749 : GaussianRat :=
  ⟨82196967/1000000000, 136904929/500000000⟩
def contact3749 : RatBall := localContactBall tau3749 center3749
def work3749 : RoundedTauEval :=
  evalTau precision tau3749 contact3749 logTwoBall

theorem center_sq3749 : (center3749.re : ℝ)^2 +
    (center3749.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3749]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3749 : work3749.theta.ok = true ∧
    work3749.jac.invOK = true ∧ acceptsUnitSq work3749.out = true := by
  norm_num [work3749, contact3749, tau3749, center3749, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3749 : CellCertificate where
  tauBall := tau3749
  contactCenter := center3749
  contactBall := contact3749
  work := work3749
  center_sq := center_sq3749
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3749.1
  jac_ok := checks3749.2.1
  accepted := checks3749.2.2

def tau3750 : RatBall :=
  ⟨⟨67/640, 243/640⟩, 3/1280⟩
def center3750 : GaussianRat :=
  ⟨42344767/500000000, 273575317/1000000000⟩
def contact3750 : RatBall := localContactBall tau3750 center3750
def work3750 : RoundedTauEval :=
  evalTau precision tau3750 contact3750 logTwoBall

theorem center_sq3750 : (center3750.re : ℝ)^2 +
    (center3750.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3750]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3750 : work3750.theta.ok = true ∧
    work3750.jac.invOK = true ∧ acceptsUnitSq work3750.out = true := by
  norm_num [work3750, contact3750, tau3750, center3750, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3750 : CellCertificate where
  tauBall := tau3750
  contactCenter := center3750
  contactBall := contact3750
  work := work3750
  center_sq := center_sq3750
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3750.1
  jac_ok := checks3750.2.1
  accepted := checks3750.2.2

def tau3751 : RatBall :=
  ⟨⟨69/640, 241/640⟩, 3/1280⟩
def center3751 : GaussianRat :=
  ⟨10867009/125000000, 67712443/250000000⟩
def contact3751 : RatBall := localContactBall tau3751 center3751
def work3751 : RoundedTauEval :=
  evalTau precision tau3751 contact3751 logTwoBall

theorem center_sq3751 : (center3751.re : ℝ)^2 +
    (center3751.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3751]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3751 : work3751.theta.ok = true ∧
    work3751.jac.invOK = true ∧ acceptsUnitSq work3751.out = true := by
  norm_num [work3751, contact3751, tau3751, center3751, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3751 : CellCertificate where
  tauBall := tau3751
  contactCenter := center3751
  contactBall := contact3751
  work := work3751
  center_sq := center_sq3751
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3751.1
  jac_ok := checks3751.2.1
  accepted := checks3751.2.2

def cells : List CellCertificate := [cell3744, cell3745, cell3746, cell3747, cell3748, cell3749, cell3750, cell3751]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468
