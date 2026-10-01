import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0472 : RatBall :=
  ⟨⟨-5/32, -37/160⟩, 3/320⟩
def center0472 : GaussianRat :=
  ⟨-113439149/1000000000, -158939613/1000000000⟩
def contact0472 : RatBall := localContactBall tau0472 center0472
def work0472 : RoundedTauEval :=
  evalTau precision tau0472 contact0472 logTwoBall

theorem center_sq0472 : (center0472.re : ℝ)^2 +
    (center0472.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0472]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0472 : work0472.theta.ok = true ∧
    work0472.jac.invOK = true ∧ acceptsUnitSq work0472.out = true := by
  norm_num [work0472, contact0472, tau0472, center0472, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0472 : CellCertificate where
  tauBall := tau0472
  contactCenter := center0472
  contactBall := contact0472
  work := work0472
  center_sq := center_sq0472
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0472.1
  jac_ok := checks0472.2.1
  accepted := checks0472.2.2

def tau0473 : RatBall :=
  ⟨⟨-3/32, -47/160⟩, 3/320⟩
def center0473 : GaussianRat :=
  ⟨-71049459/1000000000, -207833009/1000000000⟩
def contact0473 : RatBall := localContactBall tau0473 center0473
def work0473 : RoundedTauEval :=
  evalTau precision tau0473 contact0473 logTwoBall

theorem center_sq0473 : (center0473.re : ℝ)^2 +
    (center0473.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0473]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0473 : work0473.theta.ok = true ∧
    work0473.jac.invOK = true ∧ acceptsUnitSq work0473.out = true := by
  norm_num [work0473, contact0473, tau0473, center0473, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0473 : CellCertificate where
  tauBall := tau0473
  contactCenter := center0473
  contactBall := contact0473
  work := work0473
  center_sq := center_sq0473
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0473.1
  jac_ok := checks0473.2.1
  accepted := checks0473.2.2

def tau0474 : RatBall :=
  ⟨⟨-13/160, -47/160⟩, 3/320⟩
def center0474 : GaussianRat :=
  ⟨-61646237/1000000000, -5209469/25000000⟩
def contact0474 : RatBall := localContactBall tau0474 center0474
def work0474 : RoundedTauEval :=
  evalTau precision tau0474 contact0474 logTwoBall

theorem center_sq0474 : (center0474.re : ℝ)^2 +
    (center0474.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0474]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0474 : work0474.theta.ok = true ∧
    work0474.jac.invOK = true ∧ acceptsUnitSq work0474.out = true := by
  norm_num [work0474, contact0474, tau0474, center0474, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0474 : CellCertificate where
  tauBall := tau0474
  contactCenter := center0474
  contactBall := contact0474
  work := work0474
  center_sq := center_sq0474
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0474.1
  jac_ok := checks0474.2.1
  accepted := checks0474.2.2

def tau0475 : RatBall :=
  ⟨⟨-3/32, -9/32⟩, 3/320⟩
def center0475 : GaussianRat :=
  ⟨-17620809/250000000, -24810311/125000000⟩
def contact0475 : RatBall := localContactBall tau0475 center0475
def work0475 : RoundedTauEval :=
  evalTau precision tau0475 contact0475 logTwoBall

theorem center_sq0475 : (center0475.re : ℝ)^2 +
    (center0475.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0475]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0475 : work0475.theta.ok = true ∧
    work0475.jac.invOK = true ∧ acceptsUnitSq work0475.out = true := by
  norm_num [work0475, contact0475, tau0475, center0475, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0475 : CellCertificate where
  tauBall := tau0475
  contactCenter := center0475
  contactBall := contact0475
  work := work0475
  center_sq := center_sq0475
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0475.1
  jac_ok := checks0475.2.1
  accepted := checks0475.2.2

def tau0476 : RatBall :=
  ⟨⟨-13/160, -9/32⟩, 3/320⟩
def center0476 : GaussianRat :=
  ⟨-30576347/500000000, -99498463/500000000⟩
def contact0476 : RatBall := localContactBall tau0476 center0476
def work0476 : RoundedTauEval :=
  evalTau precision tau0476 contact0476 logTwoBall

theorem center_sq0476 : (center0476.re : ℝ)^2 +
    (center0476.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0476]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0476 : work0476.theta.ok = true ∧
    work0476.jac.invOK = true ∧ acceptsUnitSq work0476.out = true := by
  norm_num [work0476, contact0476, tau0476, center0476, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0476 : CellCertificate where
  tauBall := tau0476
  contactCenter := center0476
  contactBall := contact0476
  work := work0476
  center_sq := center_sq0476
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0476.1
  jac_ok := checks0476.2.1
  accepted := checks0476.2.2

def tau0477 : RatBall :=
  ⟨⟨-11/160, -47/160⟩, 3/320⟩
def center0477 : GaussianRat :=
  ⟨-13053307/250000000, -208849073/1000000000⟩
def contact0477 : RatBall := localContactBall tau0477 center0477
def work0477 : RoundedTauEval :=
  evalTau precision tau0477 contact0477 logTwoBall

theorem center_sq0477 : (center0477.re : ℝ)^2 +
    (center0477.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0477]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0477 : work0477.theta.ok = true ∧
    work0477.jac.invOK = true ∧ acceptsUnitSq work0477.out = true := by
  norm_num [work0477, contact0477, tau0477, center0477, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0477 : CellCertificate where
  tauBall := tau0477
  contactCenter := center0477
  contactBall := contact0477
  work := work0477
  center_sq := center_sq0477
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0477.1
  jac_ok := checks0477.2.1
  accepted := checks0477.2.2

def tau0478 : RatBall :=
  ⟨⟨-9/160, -47/160⟩, 3/320⟩
def center0478 : GaussianRat :=
  ⟨-42754839/1000000000, -41848559/200000000⟩
def contact0478 : RatBall := localContactBall tau0478 center0478
def work0478 : RoundedTauEval :=
  evalTau precision tau0478 contact0478 logTwoBall

theorem center_sq0478 : (center0478.re : ℝ)^2 +
    (center0478.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0478]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0478 : work0478.theta.ok = true ∧
    work0478.jac.invOK = true ∧ acceptsUnitSq work0478.out = true := by
  norm_num [work0478, contact0478, tau0478, center0478, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0478 : CellCertificate where
  tauBall := tau0478
  contactCenter := center0478
  contactBall := contact0478
  work := work0478
  center_sq := center_sq0478
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0478.1
  jac_ok := checks0478.2.1
  accepted := checks0478.2.2

def tau0479 : RatBall :=
  ⟨⟨-11/160, -9/32⟩, 3/320⟩
def center0479 : GaussianRat :=
  ⟨-25896777/500000000, -199440199/1000000000⟩
def contact0479 : RatBall := localContactBall tau0479 center0479
def work0479 : RoundedTauEval :=
  evalTau precision tau0479 contact0479 logTwoBall

theorem center_sq0479 : (center0479.re : ℝ)^2 +
    (center0479.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0479]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0479 : work0479.theta.ok = true ∧
    work0479.jac.invOK = true ∧ acceptsUnitSq work0479.out = true := by
  norm_num [work0479, contact0479, tau0479, center0479, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0479 : CellCertificate where
  tauBall := tau0479
  contactCenter := center0479
  contactBall := contact0479
  work := work0479
  center_sq := center_sq0479
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0479.1
  jac_ok := checks0479.2.1
  accepted := checks0479.2.2

def cells : List CellCertificate := [cell0472, cell0473, cell0474, cell0475, cell0476, cell0477, cell0478, cell0479]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059
