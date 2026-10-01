import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3072 : RatBall :=
  ⟨⟨77/640, -241/640⟩, 3/1280⟩
def center3072 : GaussianRat :=
  ⟨96833401/1000000000, -8432309/31250000⟩
def contact3072 : RatBall := localContactBall tau3072 center3072
def work3072 : RoundedTauEval :=
  evalTau precision tau3072 contact3072 logTwoBall

theorem center_sq3072 : (center3072.re : ℝ)^2 +
    (center3072.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3072]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3072 : work3072.theta.ok = true ∧
    work3072.jac.invOK = true ∧ acceptsUnitSq work3072.out = true := by
  norm_num [work3072, contact3072, tau3072, center3072, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3072 : CellCertificate where
  tauBall := tau3072
  contactCenter := center3072
  contactBall := contact3072
  work := work3072
  center_sq := center_sq3072
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3072.1
  jac_ok := checks3072.2.1
  accepted := checks3072.2.2

def tau3073 : RatBall :=
  ⟨⟨79/640, -241/640⟩, 3/1280⟩
def center3073 : GaussianRat :=
  ⟨99298877/1000000000, -134782023/500000000⟩
def contact3073 : RatBall := localContactBall tau3073 center3073
def work3073 : RoundedTauEval :=
  evalTau precision tau3073 contact3073 logTwoBall

theorem center_sq3073 : (center3073.re : ℝ)^2 +
    (center3073.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3073]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3073 : work3073.theta.ok = true ∧
    work3073.jac.invOK = true ∧ acceptsUnitSq work3073.out = true := by
  norm_num [work3073, contact3073, tau3073, center3073, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3073 : CellCertificate where
  tauBall := tau3073
  contactCenter := center3073
  contactBall := contact3073
  work := work3073
  center_sq := center_sq3073
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3073.1
  jac_ok := checks3073.2.1
  accepted := checks3073.2.2

def tau3074 : RatBall :=
  ⟨⟨81/640, -243/640⟩, 3/1280⟩
def center3074 : GaussianRat :=
  ⟨51020881/500000000, -135875479/500000000⟩
def contact3074 : RatBall := localContactBall tau3074 center3074
def work3074 : RoundedTauEval :=
  evalTau precision tau3074 contact3074 logTwoBall

theorem center_sq3074 : (center3074.re : ℝ)^2 +
    (center3074.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3074]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3074 : work3074.theta.ok = true ∧
    work3074.jac.invOK = true ∧ acceptsUnitSq work3074.out = true := by
  norm_num [work3074, contact3074, tau3074, center3074, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3074 : CellCertificate where
  tauBall := tau3074
  contactCenter := center3074
  contactBall := contact3074
  work := work3074
  center_sq := center_sq3074
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3074.1
  jac_ok := checks3074.2.1
  accepted := checks3074.2.2

def tau3075 : RatBall :=
  ⟨⟨83/640, -243/640⟩, 3/1280⟩
def center3075 : GaussianRat :=
  ⟨4180239/40000000, -271464801/1000000000⟩
def contact3075 : RatBall := localContactBall tau3075 center3075
def work3075 : RoundedTauEval :=
  evalTau precision tau3075 contact3075 logTwoBall

theorem center_sq3075 : (center3075.re : ℝ)^2 +
    (center3075.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3075]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3075 : work3075.theta.ok = true ∧
    work3075.jac.invOK = true ∧ acceptsUnitSq work3075.out = true := by
  norm_num [work3075, contact3075, tau3075, center3075, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3075 : CellCertificate where
  tauBall := tau3075
  contactCenter := center3075
  contactBall := contact3075
  work := work3075
  center_sq := center_sq3075
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3075.1
  jac_ok := checks3075.2.1
  accepted := checks3075.2.2

def tau3076 : RatBall :=
  ⟨⟨81/640, -241/640⟩, 3/1280⟩
def center3076 : GaussianRat :=
  ⟨101760649/1000000000, -269287947/1000000000⟩
def contact3076 : RatBall := localContactBall tau3076 center3076
def work3076 : RoundedTauEval :=
  evalTau precision tau3076 contact3076 logTwoBall

theorem center_sq3076 : (center3076.re : ℝ)^2 +
    (center3076.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3076]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3076 : work3076.theta.ok = true ∧
    work3076.jac.invOK = true ∧ acceptsUnitSq work3076.out = true := by
  norm_num [work3076, contact3076, tau3076, center3076, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3076 : CellCertificate where
  tauBall := tau3076
  contactCenter := center3076
  contactBall := contact3076
  work := work3076
  center_sq := center_sq3076
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3076.1
  jac_ok := checks3076.2.1
  accepted := checks3076.2.2

def tau3077 : RatBall :=
  ⟨⟨83/640, -241/640⟩, 3/1280⟩
def center3077 : GaussianRat :=
  ⟨104218637/1000000000, -134502819/500000000⟩
def contact3077 : RatBall := localContactBall tau3077 center3077
def work3077 : RoundedTauEval :=
  evalTau precision tau3077 contact3077 logTwoBall

theorem center_sq3077 : (center3077.re : ℝ)^2 +
    (center3077.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3077]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3077 : work3077.theta.ok = true ∧
    work3077.jac.invOK = true ∧ acceptsUnitSq work3077.out = true := by
  norm_num [work3077, contact3077, tau3077, center3077, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3077 : CellCertificate where
  tauBall := tau3077
  contactCenter := center3077
  contactBall := contact3077
  work := work3077
  center_sq := center_sq3077
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3077.1
  jac_ok := checks3077.2.1
  accepted := checks3077.2.2

def tau3078 : RatBall :=
  ⟨⟨17/128, -241/640⟩, 3/1280⟩
def center3078 : GaussianRat :=
  ⟨53336381/500000000, -268717167/1000000000⟩
def contact3078 : RatBall := localContactBall tau3078 center3078
def work3078 : RoundedTauEval :=
  evalTau precision tau3078 contact3078 logTwoBall

theorem center_sq3078 : (center3078.re : ℝ)^2 +
    (center3078.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3078]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3078 : work3078.theta.ok = true ∧
    work3078.jac.invOK = true ∧ acceptsUnitSq work3078.out = true := by
  norm_num [work3078, contact3078, tau3078, center3078, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3078 : CellCertificate where
  tauBall := tau3078
  contactCenter := center3078
  contactBall := contact3078
  work := work3078
  center_sq := center_sq3078
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3078.1
  jac_ok := checks3078.2.1
  accepted := checks3078.2.2

def tau3079 : RatBall :=
  ⟨⟨87/640, -241/640⟩, 3/1280⟩
def center3079 : GaussianRat :=
  ⟨109122947/1000000000, -53684517/200000000⟩
def contact3079 : RatBall := localContactBall tau3079 center3079
def work3079 : RoundedTauEval :=
  evalTau precision tau3079 contact3079 logTwoBall

theorem center_sq3079 : (center3079.re : ℝ)^2 +
    (center3079.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3079]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3079 : work3079.theta.ok = true ∧
    work3079.jac.invOK = true ∧ acceptsUnitSq work3079.out = true := by
  norm_num [work3079, contact3079, tau3079, center3079, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3079 : CellCertificate where
  tauBall := tau3079
  contactCenter := center3079
  contactBall := contact3079
  work := work3079
  center_sq := center_sq3079
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3079.1
  jac_ok := checks3079.2.1
  accepted := checks3079.2.2

def cells : List CellCertificate := [cell3072, cell3073, cell3074, cell3075, cell3076, cell3077, cell3078, cell3079]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384
