import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3352 : RatBall :=
  ⟨⟨-13/128, 243/640⟩, 3/1280⟩
def center3352 : GaussianRat :=
  ⟨-82196967/1000000000, 136904929/500000000⟩
def contact3352 : RatBall := localContactBall tau3352 center3352
def work3352 : RoundedTauEval :=
  evalTau precision tau3352 contact3352 logTwoBall

theorem center_sq3352 : (center3352.re : ℝ)^2 +
    (center3352.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3352]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3352 : work3352.theta.ok = true ∧
    work3352.jac.invOK = true ∧ acceptsUnitSq work3352.out = true := by
  norm_num [work3352, contact3352, tau3352, center3352, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3352 : CellCertificate where
  tauBall := tau3352
  contactCenter := center3352
  contactBall := contact3352
  work := work3352
  center_sq := center_sq3352
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3352.1
  jac_ok := checks3352.2.1
  accepted := checks3352.2.2

def tau3353 : RatBall :=
  ⟨⟨-71/640, 49/128⟩, 3/1280⟩
def center3353 : GaussianRat :=
  ⟨-44958767/500000000, 275574013/1000000000⟩
def contact3353 : RatBall := localContactBall tau3353 center3353
def work3353 : RoundedTauEval :=
  evalTau precision tau3353 contact3353 logTwoBall

theorem center_sq3353 : (center3353.re : ℝ)^2 +
    (center3353.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3353]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3353 : work3353.theta.ok = true ∧
    work3353.jac.invOK = true ∧ acceptsUnitSq work3353.out = true := by
  norm_num [work3353, contact3353, tau3353, center3353, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3353 : CellCertificate where
  tauBall := tau3353
  contactCenter := center3353
  contactBall := contact3353
  work := work3353
  center_sq := center_sq3353
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3353.1
  jac_ok := checks3353.2.1
  accepted := checks3353.2.2

def tau3354 : RatBall :=
  ⟨⟨-69/640, 49/128⟩, 3/1280⟩
def center3354 : GaussianRat :=
  ⟨-43712483/500000000, 34478141/125000000⟩
def contact3354 : RatBall := localContactBall tau3354 center3354
def work3354 : RoundedTauEval :=
  evalTau precision tau3354 contact3354 logTwoBall

theorem center_sq3354 : (center3354.re : ℝ)^2 +
    (center3354.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3354]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3354 : work3354.theta.ok = true ∧
    work3354.jac.invOK = true ∧ acceptsUnitSq work3354.out = true := by
  norm_num [work3354, contact3354, tau3354, center3354, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3354 : CellCertificate where
  tauBall := tau3354
  contactCenter := center3354
  contactBall := contact3354
  work := work3354
  center_sq := center_sq3354
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3354.1
  jac_ok := checks3354.2.1
  accepted := checks3354.2.2

def tau3355 : RatBall :=
  ⟨⟨-71/640, 247/640⟩, 3/1280⟩
def center3355 : GaussianRat :=
  ⟨-90173701/1000000000, 278068181/1000000000⟩
def contact3355 : RatBall := localContactBall tau3355 center3355
def work3355 : RoundedTauEval :=
  evalTau precision tau3355 contact3355 logTwoBall

theorem center_sq3355 : (center3355.re : ℝ)^2 +
    (center3355.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3355]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3355 : work3355.theta.ok = true ∧
    work3355.jac.invOK = true ∧ acceptsUnitSq work3355.out = true := by
  norm_num [work3355, contact3355, tau3355, center3355, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3355 : CellCertificate where
  tauBall := tau3355
  contactCenter := center3355
  contactBall := contact3355
  work := work3355
  center_sq := center_sq3355
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3355.1
  jac_ok := checks3355.2.1
  accepted := checks3355.2.2

def tau3356 : RatBall :=
  ⟨⟨-69/640, 247/640⟩, 3/1280⟩
def center3356 : GaussianRat :=
  ⟨-87674459/1000000000, 278322741/1000000000⟩
def contact3356 : RatBall := localContactBall tau3356 center3356
def work3356 : RoundedTauEval :=
  evalTau precision tau3356 contact3356 logTwoBall

theorem center_sq3356 : (center3356.re : ℝ)^2 +
    (center3356.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3356]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3356 : work3356.theta.ok = true ∧
    work3356.jac.invOK = true ∧ acceptsUnitSq work3356.out = true := by
  norm_num [work3356, contact3356, tau3356, center3356, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3356 : CellCertificate where
  tauBall := tau3356
  contactCenter := center3356
  contactBall := contact3356
  work := work3356
  center_sq := center_sq3356
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3356.1
  jac_ok := checks3356.2.1
  accepted := checks3356.2.2

def tau3357 : RatBall :=
  ⟨⟨-67/640, 49/128⟩, 3/1280⟩
def center3357 : GaussianRat :=
  ⟨-42464509/500000000, 34508699/125000000⟩
def contact3357 : RatBall := localContactBall tau3357 center3357
def work3357 : RoundedTauEval :=
  evalTau precision tau3357 contact3357 logTwoBall

theorem center_sq3357 : (center3357.re : ℝ)^2 +
    (center3357.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3357]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3357 : work3357.theta.ok = true ∧
    work3357.jac.invOK = true ∧ acceptsUnitSq work3357.out = true := by
  norm_num [work3357, contact3357, tau3357, center3357, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3357 : CellCertificate where
  tauBall := tau3357
  contactCenter := center3357
  contactBall := contact3357
  work := work3357
  center_sq := center_sq3357
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3357.1
  jac_ok := checks3357.2.1
  accepted := checks3357.2.2

def tau3358 : RatBall :=
  ⟨⟨-13/128, 49/128⟩, 3/1280⟩
def center3358 : GaussianRat :=
  ⟨-41214889/500000000, 1726921/6250000⟩
def contact3358 : RatBall := localContactBall tau3358 center3358
def work3358 : RoundedTauEval :=
  evalTau precision tau3358 contact3358 logTwoBall

theorem center_sq3358 : (center3358.re : ℝ)^2 +
    (center3358.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3358]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3358 : work3358.theta.ok = true ∧
    work3358.jac.invOK = true ∧ acceptsUnitSq work3358.out = true := by
  norm_num [work3358, contact3358, tau3358, center3358, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3358 : CellCertificate where
  tauBall := tau3358
  contactCenter := center3358
  contactBall := contact3358
  work := work3358
  center_sq := center_sq3358
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3358.1
  jac_ok := checks3358.2.1
  accepted := checks3358.2.2

def tau3359 : RatBall :=
  ⟨⟨-67/640, 247/640⟩, 3/1280⟩
def center3359 : GaussianRat :=
  ⟨-42585897/500000000, 278570563/1000000000⟩
def contact3359 : RatBall := localContactBall tau3359 center3359
def work3359 : RoundedTauEval :=
  evalTau precision tau3359 contact3359 logTwoBall

theorem center_sq3359 : (center3359.re : ℝ)^2 +
    (center3359.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3359]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3359 : work3359.theta.ok = true ∧
    work3359.jac.invOK = true ∧ acceptsUnitSq work3359.out = true := by
  norm_num [work3359, contact3359, tau3359, center3359, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3359 : CellCertificate where
  tauBall := tau3359
  contactCenter := center3359
  contactBall := contact3359
  work := work3359
  center_sq := center_sq3359
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3359.1
  jac_ok := checks3359.2.1
  accepted := checks3359.2.2

def cells : List CellCertificate := [cell3352, cell3353, cell3354, cell3355, cell3356, cell3357, cell3358, cell3359]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419
