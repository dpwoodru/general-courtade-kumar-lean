import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0288 : RatBall :=
  ⟨⟨23/80, 1/80⟩, 3/160⟩
def center0288 : GaussianRat :=
  ⟨7754861/40000000, 3988989/500000000⟩
def contact0288 : RatBall := localContactBall tau0288 center0288
def work0288 : RoundedTauEval :=
  evalTau precision tau0288 contact0288 logTwoBall

theorem center_sq0288 : (center0288.re : ℝ)^2 +
    (center0288.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0288]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0288 : work0288.theta.ok = true ∧
    work0288.jac.invOK = true ∧ acceptsUnitSq work0288.out = true := by
  norm_num [work0288, contact0288, tau0288, center0288, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0288 : CellCertificate where
  tauBall := tau0288
  contactCenter := center0288
  contactBall := contact0288
  work := work0288
  center_sq := center_sq0288
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0288.1
  jac_ok := checks0288.2.1
  accepted := checks0288.2.2

def tau0289 : RatBall :=
  ⟨⟨21/80, 3/80⟩, 3/160⟩
def center0289 : GaussianRat :=
  ⟨89006593/500000000, 4852281/200000000⟩
def contact0289 : RatBall := localContactBall tau0289 center0289
def work0289 : RoundedTauEval :=
  evalTau precision tau0289 contact0289 logTwoBall

theorem center_sq0289 : (center0289.re : ℝ)^2 +
    (center0289.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0289]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0289 : work0289.theta.ok = true ∧
    work0289.jac.invOK = true ∧ acceptsUnitSq work0289.out = true := by
  norm_num [work0289, contact0289, tau0289, center0289, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0289 : CellCertificate where
  tauBall := tau0289
  contactCenter := center0289
  contactBall := contact0289
  work := work0289
  center_sq := center_sq0289
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0289.1
  jac_ok := checks0289.2.1
  accepted := checks0289.2.2

def tau0290 : RatBall :=
  ⟨⟨23/80, 3/80⟩, 3/160⟩
def center0290 : GaussianRat :=
  ⟨4852301/25000000, 23940531/1000000000⟩
def contact0290 : RatBall := localContactBall tau0290 center0290
def work0290 : RoundedTauEval :=
  evalTau precision tau0290 contact0290 logTwoBall

theorem center_sq0290 : (center0290.re : ℝ)^2 +
    (center0290.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0290]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0290 : work0290.theta.ok = true ∧
    work0290.jac.invOK = true ∧ acceptsUnitSq work0290.out = true := by
  norm_num [work0290, contact0290, tau0290, center0290, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0290 : CellCertificate where
  tauBall := tau0290
  contactCenter := center0290
  contactBall := contact0290
  work := work0290
  center_sq := center_sq0290
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0290.1
  jac_ok := checks0290.2.1
  accepted := checks0290.2.2

def tau0291 : RatBall :=
  ⟨⟨17/80, 1/16⟩, 3/160⟩
def center0291 : GaussianRat :=
  ⟨29119789/200000000, 10355411/250000000⟩
def contact0291 : RatBall := localContactBall tau0291 center0291
def work0291 : RoundedTauEval :=
  evalTau precision tau0291 contact0291 logTwoBall

theorem center_sq0291 : (center0291.re : ℝ)^2 +
    (center0291.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0291]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0291 : work0291.theta.ok = true ∧
    work0291.jac.invOK = true ∧ acceptsUnitSq work0291.out = true := by
  norm_num [work0291, contact0291, tau0291, center0291, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0291 : CellCertificate where
  tauBall := tau0291
  contactCenter := center0291
  contactBall := contact0291
  work := work0291
  center_sq := center_sq0291
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0291.1
  jac_ok := checks0291.2.1
  accepted := checks0291.2.2

def tau0292 : RatBall :=
  ⟨⟨19/80, 1/16⟩, 3/160⟩
def center0292 : GaussianRat :=
  ⟨81055451/500000000, 40960501/1000000000⟩
def contact0292 : RatBall := localContactBall tau0292 center0292
def work0292 : RoundedTauEval :=
  evalTau precision tau0292 contact0292 logTwoBall

theorem center_sq0292 : (center0292.re : ℝ)^2 +
    (center0292.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0292]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0292 : work0292.theta.ok = true ∧
    work0292.jac.invOK = true ∧ acceptsUnitSq work0292.out = true := by
  norm_num [work0292, contact0292, tau0292, center0292, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0292 : CellCertificate where
  tauBall := tau0292
  contactCenter := center0292
  contactBall := contact0292
  work := work0292
  center_sq := center_sq0292
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0292.1
  jac_ok := checks0292.2.1
  accepted := checks0292.2.2

def tau0293 : RatBall :=
  ⟨⟨17/80, 7/80⟩, 3/160⟩
def center0293 : GaussianRat :=
  ⟨146129149/1000000000, 3628117/62500000⟩
def contact0293 : RatBall := localContactBall tau0293 center0293
def work0293 : RoundedTauEval :=
  evalTau precision tau0293 contact0293 logTwoBall

theorem center_sq0293 : (center0293.re : ℝ)^2 +
    (center0293.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0293]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0293 : work0293.theta.ok = true ∧
    work0293.jac.invOK = true ∧ acceptsUnitSq work0293.out = true := by
  norm_num [work0293, contact0293, tau0293, center0293, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0293 : CellCertificate where
  tauBall := tau0293
  contactCenter := center0293
  contactBall := contact0293
  work := work0293
  center_sq := center_sq0293
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0293.1
  jac_ok := checks0293.2.1
  accepted := checks0293.2.2

def tau0294 : RatBall :=
  ⟨⟨19/80, 7/80⟩, 3/160⟩
def center0294 : GaussianRat :=
  ⟨162690477/1000000000, 28700003/500000000⟩
def contact0294 : RatBall := localContactBall tau0294 center0294
def work0294 : RoundedTauEval :=
  evalTau precision tau0294 contact0294 logTwoBall

theorem center_sq0294 : (center0294.re : ℝ)^2 +
    (center0294.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0294]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0294 : work0294.theta.ok = true ∧
    work0294.jac.invOK = true ∧ acceptsUnitSq work0294.out = true := by
  norm_num [work0294, contact0294, tau0294, center0294, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0294 : CellCertificate where
  tauBall := tau0294
  contactCenter := center0294
  contactBall := contact0294
  work := work0294
  center_sq := center_sq0294
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0294.1
  jac_ok := checks0294.2.1
  accepted := checks0294.2.2

def tau0295 : RatBall :=
  ⟨⟨21/80, 1/16⟩, 3/160⟩
def center0295 : GaussianRat :=
  ⟨35685561/200000000, 40459851/1000000000⟩
def contact0295 : RatBall := localContactBall tau0295 center0295
def work0295 : RoundedTauEval :=
  evalTau precision tau0295 contact0295 logTwoBall

theorem center_sq0295 : (center0295.re : ℝ)^2 +
    (center0295.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0295]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0295 : work0295.theta.ok = true ∧
    work0295.jac.invOK = true ∧ acceptsUnitSq work0295.out = true := by
  norm_num [work0295, contact0295, tau0295, center0295, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0295 : CellCertificate where
  tauBall := tau0295
  contactCenter := center0295
  contactBall := contact0295
  work := work0295
  center_sq := center_sq0295
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0295.1
  jac_ok := checks0295.2.1
  accepted := checks0295.2.2

def cells : List CellCertificate := [cell0288, cell0289, cell0290, cell0291, cell0292, cell0293, cell0294, cell0295]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036
