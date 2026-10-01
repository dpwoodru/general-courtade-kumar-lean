import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3176 : RatBall :=
  ⟨⟨117/640, -45/128⟩, 3/1280⟩
def center3176 : GaussianRat :=
  ⟨8903089/62500000, -244428717/1000000000⟩
def contact3176 : RatBall := localContactBall tau3176 center3176
def work3176 : RoundedTauEval :=
  evalTau precision tau3176 contact3176 logTwoBall

theorem center_sq3176 : (center3176.re : ℝ)^2 +
    (center3176.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3176 : work3176.theta.ok = true ∧
    work3176.jac.invOK = true ∧ acceptsUnitSq work3176.out = true := by
  norm_num [work3176, contact3176, tau3176, center3176, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3176 : CellCertificate where
  tauBall := tau3176
  contactCenter := center3176
  contactBall := contact3176
  work := work3176
  center_sq := center_sq3176
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3176.1
  jac_ok := checks3176.2.1
  accepted := checks3176.2.2

def tau3177 : RatBall :=
  ⟨⟨119/640, -45/128⟩, 3/1280⟩
def center3177 : GaussianRat :=
  ⟨72393537/500000000, -122041161/500000000⟩
def contact3177 : RatBall := localContactBall tau3177 center3177
def work3177 : RoundedTauEval :=
  evalTau precision tau3177 contact3177 logTwoBall

theorem center_sq3177 : (center3177.re : ℝ)^2 +
    (center3177.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3177]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3177 : work3177.theta.ok = true ∧
    work3177.jac.invOK = true ∧ acceptsUnitSq work3177.out = true := by
  norm_num [work3177, contact3177, tau3177, center3177, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3177 : CellCertificate where
  tauBall := tau3177
  contactCenter := center3177
  contactBall := contact3177
  work := work3177
  center_sq := center_sq3177
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3177.1
  jac_ok := checks3177.2.1
  accepted := checks3177.2.2

def tau3178 : RatBall :=
  ⟨⟨121/640, -227/640⟩, 3/1280⟩
def center3178 : GaussianRat :=
  ⟨147475889/1000000000, -123032099/500000000⟩
def contact3178 : RatBall := localContactBall tau3178 center3178
def work3178 : RoundedTauEval :=
  evalTau precision tau3178 contact3178 logTwoBall

theorem center_sq3178 : (center3178.re : ℝ)^2 +
    (center3178.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3178]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3178 : work3178.theta.ok = true ∧
    work3178.jac.invOK = true ∧ acceptsUnitSq work3178.out = true := by
  norm_num [work3178, contact3178, tau3178, center3178, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3178 : CellCertificate where
  tauBall := tau3178
  contactCenter := center3178
  contactBall := contact3178
  work := work3178
  center_sq := center_sq3178
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3178.1
  jac_ok := checks3178.2.1
  accepted := checks3178.2.2

def tau3179 : RatBall :=
  ⟨⟨121/640, -45/128⟩, 3/1280⟩
def center3179 : GaussianRat :=
  ⟨36780017/250000000, -243731207/1000000000⟩
def contact3179 : RatBall := localContactBall tau3179 center3179
def work3179 : RoundedTauEval :=
  evalTau precision tau3179 contact3179 logTwoBall

theorem center_sq3179 : (center3179.re : ℝ)^2 +
    (center3179.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3179]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3179 : work3179.theta.ok = true ∧
    work3179.jac.invOK = true ∧ acceptsUnitSq work3179.out = true := by
  norm_num [work3179, contact3179, tau3179, center3179, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3179 : CellCertificate where
  tauBall := tau3179
  contactCenter := center3179
  contactBall := contact3179
  work := work3179
  center_sq := center_sq3179
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3179.1
  jac_ok := checks3179.2.1
  accepted := checks3179.2.2

def tau3180 : RatBall :=
  ⟨⟨123/640, -45/128⟩, 3/1280⟩
def center3180 : GaussianRat :=
  ⟨149448351/1000000000, -9735017/40000000⟩
def contact3180 : RatBall := localContactBall tau3180 center3180
def work3180 : RoundedTauEval :=
  evalTau precision tau3180 contact3180 logTwoBall

theorem center_sq3180 : (center3180.re : ℝ)^2 +
    (center3180.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3180]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3180 : work3180.theta.ok = true ∧
    work3180.jac.invOK = true ∧ acceptsUnitSq work3180.out = true := by
  norm_num [work3180, contact3180, tau3180, center3180, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3180 : CellCertificate where
  tauBall := tau3180
  contactCenter := center3180
  contactBall := contact3180
  work := work3180
  center_sq := center_sq3180
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3180.1
  jac_ok := checks3180.2.1
  accepted := checks3180.2.2

def tau3181 : RatBall :=
  ⟨⟨121/640, -223/640⟩, 3/1280⟩
def center3181 : GaussianRat :=
  ⟨146768957/1000000000, -60350721/250000000⟩
def contact3181 : RatBall := localContactBall tau3181 center3181
def work3181 : RoundedTauEval :=
  evalTau precision tau3181 contact3181 logTwoBall

theorem center_sq3181 : (center3181.re : ℝ)^2 +
    (center3181.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3181]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3181 : work3181.theta.ok = true ∧
    work3181.jac.invOK = true ∧ acceptsUnitSq work3181.out = true := by
  norm_num [work3181, contact3181, tau3181, center3181, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3181 : CellCertificate where
  tauBall := tau3181
  contactCenter := center3181
  contactBall := contact3181
  work := work3181
  center_sq := center_sq3181
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3181.1
  jac_ok := checks3181.2.1
  accepted := checks3181.2.2

def tau3182 : RatBall :=
  ⟨⟨123/640, -223/640⟩, 3/1280⟩
def center3182 : GaussianRat :=
  ⟨74546313/500000000, -120525907/500000000⟩
def contact3182 : RatBall := localContactBall tau3182 center3182
def work3182 : RoundedTauEval :=
  evalTau precision tau3182 contact3182 logTwoBall

theorem center_sq3182 : (center3182.re : ℝ)^2 +
    (center3182.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3182]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3182 : work3182.theta.ok = true ∧
    work3182.jac.invOK = true ∧ acceptsUnitSq work3182.out = true := by
  norm_num [work3182, contact3182, tau3182, center3182, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3182 : CellCertificate where
  tauBall := tau3182
  contactCenter := center3182
  contactBall := contact3182
  work := work3182
  center_sq := center_sq3182
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3182.1
  jac_ok := checks3182.2.1
  accepted := checks3182.2.2

def tau3183 : RatBall :=
  ⟨⟨121/640, -221/640⟩, 3/1280⟩
def center3183 : GaussianRat :=
  ⟨146422507/1000000000, -9563167/40000000⟩
def contact3183 : RatBall := localContactBall tau3183 center3183
def work3183 : RoundedTauEval :=
  evalTau precision tau3183 contact3183 logTwoBall

theorem center_sq3183 : (center3183.re : ℝ)^2 +
    (center3183.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3183]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3183 : work3183.theta.ok = true ∧
    work3183.jac.invOK = true ∧ acceptsUnitSq work3183.out = true := by
  norm_num [work3183, contact3183, tau3183, center3183, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3183 : CellCertificate where
  tauBall := tau3183
  contactCenter := center3183
  contactBall := contact3183
  work := work3183
  center_sq := center_sq3183
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3183.1
  jac_ok := checks3183.2.1
  accepted := checks3183.2.2

def cells : List CellCertificate := [cell3176, cell3177, cell3178, cell3179, cell3180, cell3181, cell3182, cell3183]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397
