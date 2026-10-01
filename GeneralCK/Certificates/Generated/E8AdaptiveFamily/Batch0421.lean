import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0421

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3368 : RatBall :=
  ⟨⟨-57/640, 243/640⟩, 3/1280⟩
def center3368 : GaussianRat :=
  ⟨-72195957/1000000000, 1716757/6250000⟩
def contact3368 : RatBall := localContactBall tau3368 center3368
def work3368 : RoundedTauEval :=
  evalTau precision tau3368 contact3368 logTwoBall

theorem center_sq3368 : (center3368.re : ℝ)^2 +
    (center3368.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3368]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3368 : work3368.theta.ok = true ∧
    work3368.jac.invOK = true ∧ acceptsUnitSq work3368.out = true := by
  norm_num [work3368, contact3368, tau3368, center3368, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3368 : CellCertificate where
  tauBall := tau3368
  contactCenter := center3368
  contactBall := contact3368
  work := work3368
  center_sq := center_sq3368
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3368.1
  jac_ok := checks3368.2.1
  accepted := checks3368.2.2

def tau3369 : RatBall :=
  ⟨⟨-63/640, 49/128⟩, 3/1280⟩
def center3369 : GaussianRat :=
  ⟨-39963667/500000000, 276538391/1000000000⟩
def contact3369 : RatBall := localContactBall tau3369 center3369
def work3369 : RoundedTauEval :=
  evalTau precision tau3369 contact3369 logTwoBall

theorem center_sq3369 : (center3369.re : ℝ)^2 +
    (center3369.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3369]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3369 : work3369.theta.ok = true ∧
    work3369.jac.invOK = true ∧ acceptsUnitSq work3369.out = true := by
  norm_num [work3369, contact3369, tau3369, center3369, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3369 : CellCertificate where
  tauBall := tau3369
  contactCenter := center3369
  contactBall := contact3369
  work := work3369
  center_sq := center_sq3369
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3369.1
  jac_ok := checks3369.2.1
  accepted := checks3369.2.2

def tau3370 : RatBall :=
  ⟨⟨-61/640, 49/128⟩, 3/1280⟩
def center3370 : GaussianRat :=
  ⟨-3096871/40000000, 138381321/500000000⟩
def contact3370 : RatBall := localContactBall tau3370 center3370
def work3370 : RoundedTauEval :=
  evalTau precision tau3370 contact3370 logTwoBall

theorem center_sq3370 : (center3370.re : ℝ)^2 +
    (center3370.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3370]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3370 : work3370.theta.ok = true ∧
    work3370.jac.invOK = true ∧ acceptsUnitSq work3370.out = true := by
  norm_num [work3370, contact3370, tau3370, center3370, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3370 : CellCertificate where
  tauBall := tau3370
  contactCenter := center3370
  contactBall := contact3370
  work := work3370
  center_sq := center_sq3370
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3370.1
  jac_ok := checks3370.2.1
  accepted := checks3370.2.2

def tau3371 : RatBall :=
  ⟨⟨-63/640, 247/640⟩, 3/1280⟩
def center3371 : GaussianRat :=
  ⟨-40078273/500000000, 69761453/250000000⟩
def contact3371 : RatBall := localContactBall tau3371 center3371
def work3371 : RoundedTauEval :=
  evalTau precision tau3371 contact3371 logTwoBall

theorem center_sq3371 : (center3371.re : ℝ)^2 +
    (center3371.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3371]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3371 : work3371.theta.ok = true ∧
    work3371.jac.invOK = true ∧ acceptsUnitSq work3371.out = true := by
  norm_num [work3371, contact3371, tau3371, center3371, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3371 : CellCertificate where
  tauBall := tau3371
  contactCenter := center3371
  contactBall := contact3371
  work := work3371
  center_sq := center_sq3371
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3371.1
  jac_ok := checks3371.2.1
  accepted := checks3371.2.2

def tau3372 : RatBall :=
  ⟨⟨-61/640, 247/640⟩, 3/1280⟩
def center3372 : GaussianRat :=
  ⟨-77644141/1000000000, 139636577/500000000⟩
def contact3372 : RatBall := localContactBall tau3372 center3372
def work3372 : RoundedTauEval :=
  evalTau precision tau3372 contact3372 logTwoBall

theorem center_sq3372 : (center3372.re : ℝ)^2 +
    (center3372.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3372]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3372 : work3372.theta.ok = true ∧
    work3372.jac.invOK = true ∧ acceptsUnitSq work3372.out = true := by
  norm_num [work3372, contact3372, tau3372, center3372, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3372 : CellCertificate where
  tauBall := tau3372
  contactCenter := center3372
  contactBall := contact3372
  work := work3372
  center_sq := center_sq3372
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3372.1
  jac_ok := checks3372.2.1
  accepted := checks3372.2.2

def tau3373 : RatBall :=
  ⟨⟨-59/640, 49/128⟩, 3/1280⟩
def center3373 : GaussianRat :=
  ⟨-7491319/100000000, 34622509/125000000⟩
def contact3373 : RatBall := localContactBall tau3373 center3373
def work3373 : RoundedTauEval :=
  evalTau precision tau3373 contact3373 logTwoBall

theorem center_sq3373 : (center3373.re : ℝ)^2 +
    (center3373.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3373]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3373 : work3373.theta.ok = true ∧
    work3373.jac.invOK = true ∧ acceptsUnitSq work3373.out = true := by
  norm_num [work3373, contact3373, tau3373, center3373, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3373 : CellCertificate where
  tauBall := tau3373
  contactCenter := center3373
  contactBall := contact3373
  work := work3373
  center_sq := center_sq3373
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3373.1
  jac_ok := checks3373.2.1
  accepted := checks3373.2.2

def tau3374 : RatBall :=
  ⟨⟨-57/640, 49/128⟩, 3/1280⟩
def center3374 : GaussianRat :=
  ⟨-7240167/100000000, 277190643/1000000000⟩
def contact3374 : RatBall := localContactBall tau3374 center3374
def work3374 : RoundedTauEval :=
  evalTau precision tau3374 contact3374 logTwoBall

theorem center_sq3374 : (center3374.re : ℝ)^2 +
    (center3374.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3374]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3374 : work3374.theta.ok = true ∧
    work3374.jac.invOK = true ∧ acceptsUnitSq work3374.out = true := by
  norm_num [work3374, contact3374, tau3374, center3374, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3374 : CellCertificate where
  tauBall := tau3374
  contactCenter := center3374
  contactBall := contact3374
  work := work3374
  center_sq := center_sq3374
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3374.1
  jac_ok := checks3374.2.1
  accepted := checks3374.2.2

def tau3375 : RatBall :=
  ⟨⟨-59/640, 247/640⟩, 3/1280⟩
def center3375 : GaussianRat :=
  ⟨-75128671/1000000000, 55898717/200000000⟩
def contact3375 : RatBall := localContactBall tau3375 center3375
def work3375 : RoundedTauEval :=
  evalTau precision tau3375 contact3375 logTwoBall

theorem center_sq3375 : (center3375.re : ℝ)^2 +
    (center3375.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3375]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3375 : work3375.theta.ok = true ∧
    work3375.jac.invOK = true ∧ acceptsUnitSq work3375.out = true := by
  norm_num [work3375, contact3375, tau3375, center3375, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3375 : CellCertificate where
  tauBall := tau3375
  contactCenter := center3375
  contactBall := contact3375
  work := work3375
  center_sq := center_sq3375
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3375.1
  jac_ok := checks3375.2.1
  accepted := checks3375.2.2

def cells : List CellCertificate := [cell3368, cell3369, cell3370, cell3371, cell3372, cell3373, cell3374, cell3375]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0421
