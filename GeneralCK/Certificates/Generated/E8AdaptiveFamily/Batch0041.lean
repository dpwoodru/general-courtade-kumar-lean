import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0328 : RatBall :=
  ⟨⟨1/16, 17/80⟩, 3/160⟩
def center0328 : GaussianRat :=
  ⟨22688687/500000000, 149010417/1000000000⟩
def contact0328 : RatBall := localContactBall tau0328 center0328
def work0328 : RoundedTauEval :=
  evalTau precision tau0328 contact0328 logTwoBall

theorem center_sq0328 : (center0328.re : ℝ)^2 +
    (center0328.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0328]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0328 : work0328.theta.ok = true ∧
    work0328.jac.invOK = true ∧ acceptsUnitSq work0328.out = true := by
  norm_num [work0328, contact0328, tau0328, center0328, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0328 : CellCertificate where
  tauBall := tau0328
  contactCenter := center0328
  contactBall := contact0328
  work := work0328
  center_sq := center_sq0328
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0328.1
  jac_ok := checks0328.2.1
  accepted := checks0328.2.2

def tau0329 : RatBall :=
  ⟨⟨7/80, 17/80⟩, 3/160⟩
def center0329 : GaussianRat :=
  ⟨31712973/500000000, 37096923/250000000⟩
def contact0329 : RatBall := localContactBall tau0329 center0329
def work0329 : RoundedTauEval :=
  evalTau precision tau0329 contact0329 logTwoBall

theorem center_sq0329 : (center0329.re : ℝ)^2 +
    (center0329.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0329]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0329 : work0329.theta.ok = true ∧
    work0329.jac.invOK = true ∧ acceptsUnitSq work0329.out = true := by
  norm_num [work0329, contact0329, tau0329, center0329, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0329 : CellCertificate where
  tauBall := tau0329
  contactCenter := center0329
  contactBall := contact0329
  work := work0329
  center_sq := center_sq0329
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0329.1
  jac_ok := checks0329.2.1
  accepted := checks0329.2.2

def tau0330 : RatBall :=
  ⟨⟨1/16, 19/80⟩, 3/160⟩
def center0330 : GaussianRat :=
  ⟨45935893/1000000000, 836037/5000000⟩
def contact0330 : RatBall := localContactBall tau0330 center0330
def work0330 : RoundedTauEval :=
  evalTau precision tau0330 contact0330 logTwoBall

theorem center_sq0330 : (center0330.re : ℝ)^2 +
    (center0330.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0330]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0330 : work0330.theta.ok = true ∧
    work0330.jac.invOK = true ∧ acceptsUnitSq work0330.out = true := by
  norm_num [work0330, contact0330, tau0330, center0330, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0330 : CellCertificate where
  tauBall := tau0330
  contactCenter := center0330
  contactBall := contact0330
  work := work0330
  center_sq := center_sq0330
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0330.1
  jac_ok := checks0330.2.1
  accepted := checks0330.2.2

def tau0331 : RatBall :=
  ⟨⟨7/80, 19/80⟩, 3/160⟩
def center0331 : GaussianRat :=
  ⟨32100469/500000000, 83247331/500000000⟩
def contact0331 : RatBall := localContactBall tau0331 center0331
def work0331 : RoundedTauEval :=
  evalTau precision tau0331 contact0331 logTwoBall

theorem center_sq0331 : (center0331.re : ℝ)^2 +
    (center0331.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0331]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0331 : work0331.theta.ok = true ∧
    work0331.jac.invOK = true ∧ acceptsUnitSq work0331.out = true := by
  norm_num [work0331, contact0331, tau0331, center0331, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0331 : CellCertificate where
  tauBall := tau0331
  contactCenter := center0331
  contactBall := contact0331
  work := work0331
  center_sq := center_sq0331
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0331.1
  jac_ok := checks0331.2.1
  accepted := checks0331.2.2

def tau0332 : RatBall :=
  ⟨⟨1/80, 21/80⟩, 3/160⟩
def center0332 : GaussianRat :=
  ⟨4665703/500000000, 93227751/500000000⟩
def contact0332 : RatBall := localContactBall tau0332 center0332
def work0332 : RoundedTauEval :=
  evalTau precision tau0332 contact0332 logTwoBall

theorem center_sq0332 : (center0332.re : ℝ)^2 +
    (center0332.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0332]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0332 : work0332.theta.ok = true ∧
    work0332.jac.invOK = true ∧ acceptsUnitSq work0332.out = true := by
  norm_num [work0332, contact0332, tau0332, center0332, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0332 : CellCertificate where
  tauBall := tau0332
  contactCenter := center0332
  contactBall := contact0332
  work := work0332
  center_sq := center_sq0332
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0332.1
  jac_ok := checks0332.2.1
  accepted := checks0332.2.2

def tau0333 : RatBall :=
  ⟨⟨3/80, 21/80⟩, 3/160⟩
def center0333 : GaussianRat :=
  ⟨27977261/1000000000, 186182371/1000000000⟩
def contact0333 : RatBall := localContactBall tau0333 center0333
def work0333 : RoundedTauEval :=
  evalTau precision tau0333 contact0333 logTwoBall

theorem center_sq0333 : (center0333.re : ℝ)^2 +
    (center0333.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0333]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0333 : work0333.theta.ok = true ∧
    work0333.jac.invOK = true ∧ acceptsUnitSq work0333.out = true := by
  norm_num [work0333, contact0333, tau0333, center0333, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0333 : CellCertificate where
  tauBall := tau0333
  contactCenter := center0333
  contactBall := contact0333
  work := work0333
  center_sq := center_sq0333
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0333.1
  jac_ok := checks0333.2.1
  accepted := checks0333.2.2

def tau0334 : RatBall :=
  ⟨⟨1/80, 23/80⟩, 3/160⟩
def center0334 : GaussianRat :=
  ⟨4738451/500000000, 102628961/500000000⟩
def contact0334 : RatBall := localContactBall tau0334 center0334
def work0334 : RoundedTauEval :=
  evalTau precision tau0334 contact0334 logTwoBall

theorem center_sq0334 : (center0334.re : ℝ)^2 +
    (center0334.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0334]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0334 : work0334.theta.ok = true ∧
    work0334.jac.invOK = true ∧ acceptsUnitSq work0334.out = true := by
  norm_num [work0334, contact0334, tau0334, center0334, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0334 : CellCertificate where
  tauBall := tau0334
  contactCenter := center0334
  contactBall := contact0334
  work := work0334
  center_sq := center_sq0334
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0334.1
  jac_ok := checks0334.2.1
  accepted := checks0334.2.2

def tau0335 : RatBall :=
  ⟨⟨3/80, 23/80⟩, 3/160⟩
def center0335 : GaussianRat :=
  ⟨14206169/500000000, 204949543/1000000000⟩
def contact0335 : RatBall := localContactBall tau0335 center0335
def work0335 : RoundedTauEval :=
  evalTau precision tau0335 contact0335 logTwoBall

theorem center_sq0335 : (center0335.re : ℝ)^2 +
    (center0335.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0335]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0335 : work0335.theta.ok = true ∧
    work0335.jac.invOK = true ∧ acceptsUnitSq work0335.out = true := by
  norm_num [work0335, contact0335, tau0335, center0335, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0335 : CellCertificate where
  tauBall := tau0335
  contactCenter := center0335
  contactBall := contact0335
  work := work0335
  center_sq := center_sq0335
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0335.1
  jac_ok := checks0335.2.1
  accepted := checks0335.2.2

def cells : List CellCertificate := [cell0328, cell0329, cell0330, cell0331, cell0332, cell0333, cell0334, cell0335]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041
