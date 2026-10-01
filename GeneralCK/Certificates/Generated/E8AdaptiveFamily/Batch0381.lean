import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3048 : RatBall :=
  ⟨⟨67/640, -247/640⟩, 3/1280⟩
def center3048 : GaussianRat :=
  ⟨42585897/500000000, -278570563/1000000000⟩
def contact3048 : RatBall := localContactBall tau3048 center3048
def work3048 : RoundedTauEval :=
  evalTau precision tau3048 contact3048 logTwoBall

theorem center_sq3048 : (center3048.re : ℝ)^2 +
    (center3048.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3048]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3048 : work3048.theta.ok = true ∧
    work3048.jac.invOK = true ∧ acceptsUnitSq work3048.out = true := by
  norm_num [work3048, contact3048, tau3048, center3048, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3048 : CellCertificate where
  tauBall := tau3048
  contactCenter := center3048
  contactBall := contact3048
  work := work3048
  center_sq := center_sq3048
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3048.1
  jac_ok := checks3048.2.1
  accepted := checks3048.2.2

def tau3049 : RatBall :=
  ⟨⟨13/128, -49/128⟩, 3/1280⟩
def center3049 : GaussianRat :=
  ⟨41214889/500000000, -1726921/6250000⟩
def contact3049 : RatBall := localContactBall tau3049 center3049
def work3049 : RoundedTauEval :=
  evalTau precision tau3049 contact3049 logTwoBall

theorem center_sq3049 : (center3049.re : ℝ)^2 +
    (center3049.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3049]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3049 : work3049.theta.ok = true ∧
    work3049.jac.invOK = true ∧ acceptsUnitSq work3049.out = true := by
  norm_num [work3049, contact3049, tau3049, center3049, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3049 : CellCertificate where
  tauBall := tau3049
  contactCenter := center3049
  contactBall := contact3049
  work := work3049
  center_sq := center_sq3049
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3049.1
  jac_ok := checks3049.2.1
  accepted := checks3049.2.2

def tau3050 : RatBall :=
  ⟨⟨67/640, -49/128⟩, 3/1280⟩
def center3050 : GaussianRat :=
  ⟨42464509/500000000, -34508699/125000000⟩
def contact3050 : RatBall := localContactBall tau3050 center3050
def work3050 : RoundedTauEval :=
  evalTau precision tau3050 contact3050 logTwoBall

theorem center_sq3050 : (center3050.re : ℝ)^2 +
    (center3050.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3050]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3050 : work3050.theta.ok = true ∧
    work3050.jac.invOK = true ∧ acceptsUnitSq work3050.out = true := by
  norm_num [work3050, contact3050, tau3050, center3050, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3050 : CellCertificate where
  tauBall := tau3050
  contactCenter := center3050
  contactBall := contact3050
  work := work3050
  center_sq := center_sq3050
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3050.1
  jac_ok := checks3050.2.1
  accepted := checks3050.2.2

def tau3051 : RatBall :=
  ⟨⟨69/640, -247/640⟩, 3/1280⟩
def center3051 : GaussianRat :=
  ⟨87674459/1000000000, -278322741/1000000000⟩
def contact3051 : RatBall := localContactBall tau3051 center3051
def work3051 : RoundedTauEval :=
  evalTau precision tau3051 contact3051 logTwoBall

theorem center_sq3051 : (center3051.re : ℝ)^2 +
    (center3051.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3051]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3051 : work3051.theta.ok = true ∧
    work3051.jac.invOK = true ∧ acceptsUnitSq work3051.out = true := by
  norm_num [work3051, contact3051, tau3051, center3051, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3051 : CellCertificate where
  tauBall := tau3051
  contactCenter := center3051
  contactBall := contact3051
  work := work3051
  center_sq := center_sq3051
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3051.1
  jac_ok := checks3051.2.1
  accepted := checks3051.2.2

def tau3052 : RatBall :=
  ⟨⟨71/640, -247/640⟩, 3/1280⟩
def center3052 : GaussianRat :=
  ⟨90173701/1000000000, -278068181/1000000000⟩
def contact3052 : RatBall := localContactBall tau3052 center3052
def work3052 : RoundedTauEval :=
  evalTau precision tau3052 contact3052 logTwoBall

theorem center_sq3052 : (center3052.re : ℝ)^2 +
    (center3052.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3052]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3052 : work3052.theta.ok = true ∧
    work3052.jac.invOK = true ∧ acceptsUnitSq work3052.out = true := by
  norm_num [work3052, contact3052, tau3052, center3052, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3052 : CellCertificate where
  tauBall := tau3052
  contactCenter := center3052
  contactBall := contact3052
  work := work3052
  center_sq := center_sq3052
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3052.1
  jac_ok := checks3052.2.1
  accepted := checks3052.2.2

def tau3053 : RatBall :=
  ⟨⟨69/640, -49/128⟩, 3/1280⟩
def center3053 : GaussianRat :=
  ⟨43712483/500000000, -34478141/125000000⟩
def contact3053 : RatBall := localContactBall tau3053 center3053
def work3053 : RoundedTauEval :=
  evalTau precision tau3053 contact3053 logTwoBall

theorem center_sq3053 : (center3053.re : ℝ)^2 +
    (center3053.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3053]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3053 : work3053.theta.ok = true ∧
    work3053.jac.invOK = true ∧ acceptsUnitSq work3053.out = true := by
  norm_num [work3053, contact3053, tau3053, center3053, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3053 : CellCertificate where
  tauBall := tau3053
  contactCenter := center3053
  contactBall := contact3053
  work := work3053
  center_sq := center_sq3053
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3053.1
  jac_ok := checks3053.2.1
  accepted := checks3053.2.2

def tau3054 : RatBall :=
  ⟨⟨71/640, -49/128⟩, 3/1280⟩
def center3054 : GaussianRat :=
  ⟨44958767/500000000, -275574013/1000000000⟩
def contact3054 : RatBall := localContactBall tau3054 center3054
def work3054 : RoundedTauEval :=
  evalTau precision tau3054 contact3054 logTwoBall

theorem center_sq3054 : (center3054.re : ℝ)^2 +
    (center3054.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3054]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3054 : work3054.theta.ok = true ∧
    work3054.jac.invOK = true ∧ acceptsUnitSq work3054.out = true := by
  norm_num [work3054, contact3054, tau3054, center3054, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3054 : CellCertificate where
  tauBall := tau3054
  contactCenter := center3054
  contactBall := contact3054
  work := work3054
  center_sq := center_sq3054
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3054.1
  jac_ok := checks3054.2.1
  accepted := checks3054.2.2

def tau3055 : RatBall :=
  ⟨⟨13/128, -243/640⟩, 3/1280⟩
def center3055 : GaussianRat :=
  ⟨82196967/1000000000, -136904929/500000000⟩
def contact3055 : RatBall := localContactBall tau3055 center3055
def work3055 : RoundedTauEval :=
  evalTau precision tau3055 contact3055 logTwoBall

theorem center_sq3055 : (center3055.re : ℝ)^2 +
    (center3055.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3055]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3055 : work3055.theta.ok = true ∧
    work3055.jac.invOK = true ∧ acceptsUnitSq work3055.out = true := by
  norm_num [work3055, contact3055, tau3055, center3055, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3055 : CellCertificate where
  tauBall := tau3055
  contactCenter := center3055
  contactBall := contact3055
  work := work3055
  center_sq := center_sq3055
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3055.1
  jac_ok := checks3055.2.1
  accepted := checks3055.2.2

def cells : List CellCertificate := [cell3048, cell3049, cell3050, cell3051, cell3052, cell3053, cell3054, cell3055]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381
