import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0054

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0432 : RatBall :=
  ⟨⟨-1/160, -49/160⟩, 3/320⟩
def center0432 : GaussianRat :=
  ⟨-1199829/250000000, -109796019/500000000⟩
def contact0432 : RatBall := localContactBall tau0432 center0432
def work0432 : RoundedTauEval :=
  evalTau precision tau0432 contact0432 logTwoBall

theorem center_sq0432 : (center0432.re : ℝ)^2 +
    (center0432.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0432]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0432 : work0432.theta.ok = true ∧
    work0432.jac.invOK = true ∧ acceptsUnitSq work0432.out = true := by
  norm_num [work0432, contact0432, tau0432, center0432, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0432 : CellCertificate where
  tauBall := tau0432
  contactCenter := center0432
  contactBall := contact0432
  work := work0432
  center_sq := center_sq0432
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0432.1
  jac_ok := checks0432.2.1
  accepted := checks0432.2.2

def tau0433 : RatBall :=
  ⟨⟨-31/160, -47/160⟩, 3/320⟩
def center0433 : GaussianRat :=
  ⟨-5788509/40000000, -200941561/1000000000⟩
def contact0433 : RatBall := localContactBall tau0433 center0433
def work0433 : RoundedTauEval :=
  evalTau precision tau0433 contact0433 logTwoBall

theorem center_sq0433 : (center0433.re : ℝ)^2 +
    (center0433.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0433]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0433 : work0433.theta.ok = true ∧
    work0433.jac.invOK = true ∧ acceptsUnitSq work0433.out = true := by
  norm_num [work0433, contact0433, tau0433, center0433, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0433 : CellCertificate where
  tauBall := tau0433
  contactCenter := center0433
  contactBall := contact0433
  work := work0433
  center_sq := center_sq0433
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0433.1
  jac_ok := checks0433.2.1
  accepted := checks0433.2.2

def tau0434 : RatBall :=
  ⟨⟨-29/160, -47/160⟩, 3/320⟩
def center0434 : GaussianRat :=
  ⟨-135691941/1000000000, -202030811/1000000000⟩
def contact0434 : RatBall := localContactBall tau0434 center0434
def work0434 : RoundedTauEval :=
  evalTau precision tau0434 contact0434 logTwoBall

theorem center_sq0434 : (center0434.re : ℝ)^2 +
    (center0434.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0434]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0434 : work0434.theta.ok = true ∧
    work0434.jac.invOK = true ∧ acceptsUnitSq work0434.out = true := by
  norm_num [work0434, contact0434, tau0434, center0434, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0434 : CellCertificate where
  tauBall := tau0434
  contactCenter := center0434
  contactBall := contact0434
  work := work0434
  center_sq := center_sq0434
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0434.1
  jac_ok := checks0434.2.1
  accepted := checks0434.2.2

def tau0435 : RatBall :=
  ⟨⟨-31/160, -9/32⟩, 3/320⟩
def center0435 : GaussianRat :=
  ⟨-143625227/1000000000, -38396169/200000000⟩
def contact0435 : RatBall := localContactBall tau0435 center0435
def work0435 : RoundedTauEval :=
  evalTau precision tau0435 contact0435 logTwoBall

theorem center_sq0435 : (center0435.re : ℝ)^2 +
    (center0435.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0435]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0435 : work0435.theta.ok = true ∧
    work0435.jac.invOK = true ∧ acceptsUnitSq work0435.out = true := by
  norm_num [work0435, contact0435, tau0435, center0435, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0435 : CellCertificate where
  tauBall := tau0435
  contactCenter := center0435
  contactBall := contact0435
  work := work0435
  center_sq := center_sq0435
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0435.1
  jac_ok := checks0435.2.1
  accepted := checks0435.2.2

def tau0436 : RatBall :=
  ⟨⟨-29/160, -9/32⟩, 3/320⟩
def center0436 : GaussianRat :=
  ⟨-67331309/500000000, -193009163/1000000000⟩
def contact0436 : RatBall := localContactBall tau0436 center0436
def work0436 : RoundedTauEval :=
  evalTau precision tau0436 contact0436 logTwoBall

theorem center_sq0436 : (center0436.re : ℝ)^2 +
    (center0436.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0436]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0436 : work0436.theta.ok = true ∧
    work0436.jac.invOK = true ∧ acceptsUnitSq work0436.out = true := by
  norm_num [work0436, contact0436, tau0436, center0436, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0436 : CellCertificate where
  tauBall := tau0436
  contactCenter := center0436
  contactBall := contact0436
  work := work0436
  center_sq := center_sq0436
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0436.1
  jac_ok := checks0436.2.1
  accepted := checks0436.2.2

def tau0437 : RatBall :=
  ⟨⟨-27/160, -47/160⟩, 3/320⟩
def center0437 : GaussianRat :=
  ⟨-31652671/250000000, -101529593/500000000⟩
def contact0437 : RatBall := localContactBall tau0437 center0437
def work0437 : RoundedTauEval :=
  evalTau precision tau0437 contact0437 logTwoBall

theorem center_sq0437 : (center0437.re : ℝ)^2 +
    (center0437.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0437]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0437 : work0437.theta.ok = true ∧
    work0437.jac.invOK = true ∧ acceptsUnitSq work0437.out = true := by
  norm_num [work0437, contact0437, tau0437, center0437, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0437 : CellCertificate where
  tauBall := tau0437
  contactCenter := center0437
  contactBall := contact0437
  work := work0437
  center_sq := center_sq0437
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0437.1
  jac_ok := checks0437.2.1
  accepted := checks0437.2.2

def tau0438 : RatBall :=
  ⟨⟨-5/32, -47/160⟩, 3/320⟩
def center0438 : GaussianRat :=
  ⟨-58736127/500000000, -40804889/200000000⟩
def contact0438 : RatBall := localContactBall tau0438 center0438
def work0438 : RoundedTauEval :=
  evalTau precision tau0438 contact0438 logTwoBall

theorem center_sq0438 : (center0438.re : ℝ)^2 +
    (center0438.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0438]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0438 : work0438.theta.ok = true ∧
    work0438.jac.invOK = true ∧ acceptsUnitSq work0438.out = true := by
  norm_num [work0438, contact0438, tau0438, center0438, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0438 : CellCertificate where
  tauBall := tau0438
  contactCenter := center0438
  contactBall := contact0438
  work := work0438
  center_sq := center_sq0438
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0438.1
  jac_ok := checks0438.2.1
  accepted := checks0438.2.2

def tau0439 : RatBall :=
  ⟨⟨-27/160, -9/32⟩, 3/320⟩
def center0439 : GaussianRat :=
  ⟨-25128347/200000000, -9698989/50000000⟩
def contact0439 : RatBall := localContactBall tau0439 center0439
def work0439 : RoundedTauEval :=
  evalTau precision tau0439 contact0439 logTwoBall

theorem center_sq0439 : (center0439.re : ℝ)^2 +
    (center0439.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0439]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0439 : work0439.theta.ok = true ∧
    work0439.jac.invOK = true ∧ acceptsUnitSq work0439.out = true := by
  norm_num [work0439, contact0439, tau0439, center0439, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0439 : CellCertificate where
  tauBall := tau0439
  contactCenter := center0439
  contactBall := contact0439
  work := work0439
  center_sq := center_sq0439
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0439.1
  jac_ok := checks0439.2.1
  accepted := checks0439.2.2

def cells : List CellCertificate := [cell0432, cell0433, cell0434, cell0435, cell0436, cell0437, cell0438, cell0439]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0054
