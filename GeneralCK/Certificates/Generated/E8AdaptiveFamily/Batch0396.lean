import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3168 : RatBall :=
  ⟨⟨23/128, -229/640⟩, 3/1280⟩
def center3168 : GaussianRat :=
  ⟨70397387/500000000, -249469121/1000000000⟩
def contact3168 : RatBall := localContactBall tau3168 center3168
def work3168 : RoundedTauEval :=
  evalTau precision tau3168 contact3168 logTwoBall

theorem center_sq3168 : (center3168.re : ℝ)^2 +
    (center3168.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3168]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3168 : work3168.theta.ok = true ∧
    work3168.jac.invOK = true ∧ acceptsUnitSq work3168.out = true := by
  norm_num [work3168, contact3168, tau3168, center3168, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3168 : CellCertificate where
  tauBall := tau3168
  contactCenter := center3168
  contactBall := contact3168
  work := work3168
  center_sq := center_sq3168
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3168.1
  jac_ok := checks3168.2.1
  accepted := checks3168.2.2

def tau3169 : RatBall :=
  ⟨⟨117/640, -229/640⟩, 3/1280⟩
def center3169 : GaussianRat :=
  ⟨143146729/1000000000, -249118251/1000000000⟩
def contact3169 : RatBall := localContactBall tau3169 center3169
def work3169 : RoundedTauEval :=
  evalTau precision tau3169 contact3169 logTwoBall

theorem center_sq3169 : (center3169.re : ℝ)^2 +
    (center3169.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3169]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3169 : work3169.theta.ok = true ∧
    work3169.jac.invOK = true ∧ acceptsUnitSq work3169.out = true := by
  norm_num [work3169, contact3169, tau3169, center3169, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3169 : CellCertificate where
  tauBall := tau3169
  contactCenter := center3169
  contactBall := contact3169
  work := work3169
  center_sq := center_sq3169
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3169.1
  jac_ok := checks3169.2.1
  accepted := checks3169.2.2

def tau3170 : RatBall :=
  ⟨⟨113/640, -227/640⟩, 3/1280⟩
def center3170 : GaussianRat :=
  ⟨138097011/1000000000, -61864659/250000000⟩
def contact3170 : RatBall := localContactBall tau3170 center3170
def work3170 : RoundedTauEval :=
  evalTau precision tau3170 contact3170 logTwoBall

theorem center_sq3170 : (center3170.re : ℝ)^2 +
    (center3170.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3170]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3170 : work3170.theta.ok = true ∧
    work3170.jac.invOK = true ∧ acceptsUnitSq work3170.out = true := by
  norm_num [work3170, contact3170, tau3170, center3170, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3170 : CellCertificate where
  tauBall := tau3170
  contactCenter := center3170
  contactBall := contact3170
  work := work3170
  center_sq := center_sq3170
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3170.1
  jac_ok := checks3170.2.1
  accepted := checks3170.2.2

def tau3171 : RatBall :=
  ⟨⟨23/128, -227/640⟩, 3/1280⟩
def center3171 : GaussianRat :=
  ⟨140448677/1000000000, -247117293/1000000000⟩
def contact3171 : RatBall := localContactBall tau3171 center3171
def work3171 : RoundedTauEval :=
  evalTau precision tau3171 contact3171 logTwoBall

theorem center_sq3171 : (center3171.re : ℝ)^2 +
    (center3171.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3171]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3171 : work3171.theta.ok = true ∧
    work3171.jac.invOK = true ∧ acceptsUnitSq work3171.out = true := by
  norm_num [work3171, contact3171, tau3171, center3171, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3171 : CellCertificate where
  tauBall := tau3171
  contactCenter := center3171
  contactBall := contact3171
  work := work3171
  center_sq := center_sq3171
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3171.1
  jac_ok := checks3171.2.1
  accepted := checks3171.2.2

def tau3172 : RatBall :=
  ⟨⟨113/640, -45/128⟩, 3/1280⟩
def center3172 : GaussianRat :=
  ⟨137760383/1000000000, -245107147/1000000000⟩
def contact3172 : RatBall := localContactBall tau3172 center3172
def work3172 : RoundedTauEval :=
  evalTau precision tau3172 contact3172 logTwoBall

theorem center_sq3172 : (center3172.re : ℝ)^2 +
    (center3172.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3172]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3172 : work3172.theta.ok = true ∧
    work3172.jac.invOK = true ∧ acceptsUnitSq work3172.out = true := by
  norm_num [work3172, contact3172, tau3172, center3172, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3172 : CellCertificate where
  tauBall := tau3172
  contactCenter := center3172
  contactBall := contact3172
  work := work3172
  center_sq := center_sq3172
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3172.1
  jac_ok := checks3172.2.1
  accepted := checks3172.2.2

def tau3173 : RatBall :=
  ⟨⟨23/128, -45/128⟩, 3/1280⟩
def center3173 : GaussianRat :=
  ⟨5604287/40000000, -122385171/500000000⟩
def contact3173 : RatBall := localContactBall tau3173 center3173
def work3173 : RoundedTauEval :=
  evalTau precision tau3173 contact3173 logTwoBall

theorem center_sq3173 : (center3173.re : ℝ)^2 +
    (center3173.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3173]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3173 : work3173.theta.ok = true ∧
    work3173.jac.invOK = true ∧ acceptsUnitSq work3173.out = true := by
  norm_num [work3173, contact3173, tau3173, center3173, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3173 : CellCertificate where
  tauBall := tau3173
  contactCenter := center3173
  contactBall := contact3173
  work := work3173
  center_sq := center_sq3173
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3173.1
  jac_ok := checks3173.2.1
  accepted := checks3173.2.2

def tau3174 : RatBall :=
  ⟨⟨117/640, -227/640⟩, 3/1280⟩
def center3174 : GaussianRat :=
  ⟨142795751/1000000000, -246771071/1000000000⟩
def contact3174 : RatBall := localContactBall tau3174 center3174
def work3174 : RoundedTauEval :=
  evalTau precision tau3174 contact3174 logTwoBall

theorem center_sq3174 : (center3174.re : ℝ)^2 +
    (center3174.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3174]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3174 : work3174.theta.ok = true ∧
    work3174.jac.invOK = true ∧ acceptsUnitSq work3174.out = true := by
  norm_num [work3174, contact3174, tau3174, center3174, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3174 : CellCertificate where
  tauBall := tau3174
  contactCenter := center3174
  contactBall := contact3174
  work := work3174
  center_sq := center_sq3174
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3174.1
  jac_ok := checks3174.2.1
  accepted := checks3174.2.2

def tau3175 : RatBall :=
  ⟨⟨119/640, -227/640⟩, 3/1280⟩
def center3175 : GaussianRat :=
  ⟨145138173/1000000000, -123210011/500000000⟩
def contact3175 : RatBall := localContactBall tau3175 center3175
def work3175 : RoundedTauEval :=
  evalTau precision tau3175 contact3175 logTwoBall

theorem center_sq3175 : (center3175.re : ℝ)^2 +
    (center3175.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3175]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3175 : work3175.theta.ok = true ∧
    work3175.jac.invOK = true ∧ acceptsUnitSq work3175.out = true := by
  norm_num [work3175, contact3175, tau3175, center3175, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3175 : CellCertificate where
  tauBall := tau3175
  contactCenter := center3175
  contactBall := contact3175
  work := work3175
  center_sq := center_sq3175
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3175.1
  jac_ok := checks3175.2.1
  accepted := checks3175.2.2

def cells : List CellCertificate := [cell3168, cell3169, cell3170, cell3171, cell3172, cell3173, cell3174, cell3175]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396
