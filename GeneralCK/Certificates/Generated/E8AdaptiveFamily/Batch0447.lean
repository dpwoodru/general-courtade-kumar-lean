import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3576 : RatBall :=
  ⟨⟨17/640, 253/640⟩, 3/1280⟩
def center3576 : GaussianRat :=
  ⟨21961069/1000000000, 145086923/500000000⟩
def contact3576 : RatBall := localContactBall tau3576 center3576
def work3576 : RoundedTauEval :=
  evalTau precision tau3576 contact3576 logTwoBall

theorem center_sq3576 : (center3576.re : ℝ)^2 +
    (center3576.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3576]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3576 : work3576.theta.ok = true ∧
    work3576.jac.invOK = true ∧ acceptsUnitSq work3576.out = true := by
  norm_num [work3576, contact3576, tau3576, center3576, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3576 : CellCertificate where
  tauBall := tau3576
  contactCenter := center3576
  contactBall := contact3576
  work := work3576
  center_sq := center_sq3576
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3576.1
  jac_ok := checks3576.2.1
  accepted := checks3576.2.2

def tau3577 : RatBall :=
  ⟨⟨19/640, 253/640⟩, 3/1280⟩
def center3577 : GaussianRat :=
  ⟨24541601/1000000000, 290103079/1000000000⟩
def contact3577 : RatBall := localContactBall tau3577 center3577
def work3577 : RoundedTauEval :=
  evalTau precision tau3577 contact3577 logTwoBall

theorem center_sq3577 : (center3577.re : ℝ)^2 +
    (center3577.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3577]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3577 : work3577.theta.ok = true ∧
    work3577.jac.invOK = true ∧ acceptsUnitSq work3577.out = true := by
  norm_num [work3577, contact3577, tau3577, center3577, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3577 : CellCertificate where
  tauBall := tau3577
  contactCenter := center3577
  contactBall := contact3577
  work := work3577
  center_sq := center_sq3577
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3577.1
  jac_ok := checks3577.2.1
  accepted := checks3577.2.2

def tau3578 : RatBall :=
  ⟨⟨17/640, 51/128⟩, 3/1280⟩
def center3578 : GaussianRat :=
  ⟨22028391/1000000000, 146379397/500000000⟩
def contact3578 : RatBall := localContactBall tau3578 center3578
def work3578 : RoundedTauEval :=
  evalTau precision tau3578 contact3578 logTwoBall

theorem center_sq3578 : (center3578.re : ℝ)^2 +
    (center3578.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3578]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3578 : work3578.theta.ok = true ∧
    work3578.jac.invOK = true ∧ acceptsUnitSq work3578.out = true := by
  norm_num [work3578, contact3578, tau3578, center3578, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3578 : CellCertificate where
  tauBall := tau3578
  contactCenter := center3578
  contactBall := contact3578
  work := work3578
  center_sq := center_sq3578
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3578.1
  jac_ok := checks3578.2.1
  accepted := checks3578.2.2

def tau3579 : RatBall :=
  ⟨⟨19/640, 51/128⟩, 3/1280⟩
def center3579 : GaussianRat :=
  ⟨24616799/1000000000, 73171759/250000000⟩
def contact3579 : RatBall := localContactBall tau3579 center3579
def work3579 : RoundedTauEval :=
  evalTau precision tau3579 contact3579 logTwoBall

theorem center_sq3579 : (center3579.re : ℝ)^2 +
    (center3579.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3579]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3579 : work3579.theta.ok = true ∧
    work3579.jac.invOK = true ∧ acceptsUnitSq work3579.out = true := by
  norm_num [work3579, contact3579, tau3579, center3579, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3579 : CellCertificate where
  tauBall := tau3579
  contactCenter := center3579
  contactBall := contact3579
  work := work3579
  center_sq := center_sq3579
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3579.1
  jac_ok := checks3579.2.1
  accepted := checks3579.2.2

def tau3580 : RatBall :=
  ⟨⟨21/640, 253/640⟩, 3/1280⟩
def center3580 : GaussianRat :=
  ⟨5424219/200000000, 290024499/1000000000⟩
def contact3580 : RatBall := localContactBall tau3580 center3580
def work3580 : RoundedTauEval :=
  evalTau precision tau3580 contact3580 logTwoBall

theorem center_sq3580 : (center3580.re : ℝ)^2 +
    (center3580.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3580]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3580 : work3580.theta.ok = true ∧
    work3580.jac.invOK = true ∧ acceptsUnitSq work3580.out = true := by
  norm_num [work3580, contact3580, tau3580, center3580, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3580 : CellCertificate where
  tauBall := tau3580
  contactCenter := center3580
  contactBall := contact3580
  work := work3580
  center_sq := center_sq3580
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3580.1
  jac_ok := checks3580.2.1
  accepted := checks3580.2.2

def tau3581 : RatBall :=
  ⟨⟨23/640, 253/640⟩, 3/1280⟩
def center3581 : GaussianRat :=
  ⟨14849721/500000000, 7248453/25000000⟩
def contact3581 : RatBall := localContactBall tau3581 center3581
def work3581 : RoundedTauEval :=
  evalTau precision tau3581 contact3581 logTwoBall

theorem center_sq3581 : (center3581.re : ℝ)^2 +
    (center3581.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3581]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3581 : work3581.theta.ok = true ∧
    work3581.jac.invOK = true ∧ acceptsUnitSq work3581.out = true := by
  norm_num [work3581, contact3581, tau3581, center3581, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3581 : CellCertificate where
  tauBall := tau3581
  contactCenter := center3581
  contactBall := contact3581
  work := work3581
  center_sq := center_sq3581
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3581.1
  jac_ok := checks3581.2.1
  accepted := checks3581.2.2

def tau3582 : RatBall :=
  ⟨⟨21/640, 51/128⟩, 3/1280⟩
def center3582 : GaussianRat :=
  ⟨27204153/1000000000, 58521471/200000000⟩
def contact3582 : RatBall := localContactBall tau3582 center3582
def work3582 : RoundedTauEval :=
  evalTau precision tau3582 contact3582 logTwoBall

theorem center_sq3582 : (center3582.re : ℝ)^2 +
    (center3582.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3582]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3582 : work3582.theta.ok = true ∧
    work3582.jac.invOK = true ∧ acceptsUnitSq work3582.out = true := by
  norm_num [work3582, contact3582, tau3582, center3582, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3582 : CellCertificate where
  tauBall := tau3582
  contactCenter := center3582
  contactBall := contact3582
  work := work3582
  center_sq := center_sq3582
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3582.1
  jac_ok := checks3582.2.1
  accepted := checks3582.2.2

def tau3583 : RatBall :=
  ⟨⟨23/640, 51/128⟩, 3/1280⟩
def center3583 : GaussianRat :=
  ⟨5958069/200000000, 292519767/1000000000⟩
def contact3583 : RatBall := localContactBall tau3583 center3583
def work3583 : RoundedTauEval :=
  evalTau precision tau3583 contact3583 logTwoBall

theorem center_sq3583 : (center3583.re : ℝ)^2 +
    (center3583.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3583]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3583 : work3583.theta.ok = true ∧
    work3583.jac.invOK = true ∧ acceptsUnitSq work3583.out = true := by
  norm_num [work3583, contact3583, tau3583, center3583, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3583 : CellCertificate where
  tauBall := tau3583
  contactCenter := center3583
  contactBall := contact3583
  work := work3583
  center_sq := center_sq3583
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3583.1
  jac_ok := checks3583.2.1
  accepted := checks3583.2.2

def cells : List CellCertificate := [cell3576, cell3577, cell3578, cell3579, cell3580, cell3581, cell3582, cell3583]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447
