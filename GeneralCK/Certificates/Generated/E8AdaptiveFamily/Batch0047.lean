import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0376 : RatBall :=
  ⟨⟨-41/160, -33/160⟩, 3/320⟩
def center0376 : GaussianRat :=
  ⟨-180884951/1000000000, -135214257/1000000000⟩
def contact0376 : RatBall := localContactBall tau0376 center0376
def work0376 : RoundedTauEval :=
  evalTau precision tau0376 contact0376 logTwoBall

theorem center_sq0376 : (center0376.re : ℝ)^2 +
    (center0376.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0376]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0376 : work0376.theta.ok = true ∧
    work0376.jac.invOK = true ∧ acceptsUnitSq work0376.out = true := by
  norm_num [work0376, contact0376, tau0376, center0376, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0376 : CellCertificate where
  tauBall := tau0376
  contactCenter := center0376
  contactBall := contact0376
  work := work0376
  center_sq := center_sq0376
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0376.1
  jac_ok := checks0376.2.1
  accepted := checks0376.2.2

def tau0377 : RatBall :=
  ⟨⟨-39/160, -39/160⟩, 3/320⟩
def center0377 : GaussianRat :=
  ⟨-7014647/40000000, -32307527/200000000⟩
def contact0377 : RatBall := localContactBall tau0377 center0377
def work0377 : RoundedTauEval :=
  evalTau precision tau0377 contact0377 logTwoBall

theorem center_sq0377 : (center0377.re : ℝ)^2 +
    (center0377.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0377]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0377 : work0377.theta.ok = true ∧
    work0377.jac.invOK = true ∧ acceptsUnitSq work0377.out = true := by
  norm_num [work0377, contact0377, tau0377, center0377, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0377 : CellCertificate where
  tauBall := tau0377
  contactCenter := center0377
  contactBall := contact0377
  work := work0377
  center_sq := center_sq0377
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0377.1
  jac_ok := checks0377.2.1
  accepted := checks0377.2.2

def tau0378 : RatBall :=
  ⟨⟨-37/160, -39/160⟩, 3/320⟩
def center0378 : GaussianRat :=
  ⟨-83398769/500000000, -20321547/125000000⟩
def contact0378 : RatBall := localContactBall tau0378 center0378
def work0378 : RoundedTauEval :=
  evalTau precision tau0378 contact0378 logTwoBall

theorem center_sq0378 : (center0378.re : ℝ)^2 +
    (center0378.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0378]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0378 : work0378.theta.ok = true ∧
    work0378.jac.invOK = true ∧ acceptsUnitSq work0378.out = true := by
  norm_num [work0378, contact0378, tau0378, center0378, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0378 : CellCertificate where
  tauBall := tau0378
  contactCenter := center0378
  contactBall := contact0378
  work := work0378
  center_sq := center_sq0378
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0378.1
  jac_ok := checks0378.2.1
  accepted := checks0378.2.2

def tau0379 : RatBall :=
  ⟨⟨-39/160, -37/160⟩, 3/320⟩
def center0379 : GaussianRat :=
  ⟨-174343743/1000000000, -153020771/1000000000⟩
def contact0379 : RatBall := localContactBall tau0379 center0379
def work0379 : RoundedTauEval :=
  evalTau precision tau0379 contact0379 logTwoBall

theorem center_sq0379 : (center0379.re : ℝ)^2 +
    (center0379.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0379]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0379 : work0379.theta.ok = true ∧
    work0379.jac.invOK = true ∧ acceptsUnitSq work0379.out = true := by
  norm_num [work0379, contact0379, tau0379, center0379, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0379 : CellCertificate where
  tauBall := tau0379
  contactCenter := center0379
  contactBall := contact0379
  work := work0379
  center_sq := center_sq0379
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0379.1
  jac_ok := checks0379.2.1
  accepted := checks0379.2.2

def tau0380 : RatBall :=
  ⟨⟨-37/160, -37/160⟩, 3/320⟩
def center0380 : GaussianRat :=
  ⟨-33162899/200000000, -153992113/1000000000⟩
def contact0380 : RatBall := localContactBall tau0380 center0380
def work0380 : RoundedTauEval :=
  evalTau precision tau0380 contact0380 logTwoBall

theorem center_sq0380 : (center0380.re : ℝ)^2 +
    (center0380.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0380]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0380 : work0380.theta.ok = true ∧
    work0380.jac.invOK = true ∧ acceptsUnitSq work0380.out = true := by
  norm_num [work0380, contact0380, tau0380, center0380, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0380 : CellCertificate where
  tauBall := tau0380
  contactCenter := center0380
  contactBall := contact0380
  work := work0380
  center_sq := center_sq0380
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0380.1
  jac_ok := checks0380.2.1
  accepted := checks0380.2.2

def tau0381 : RatBall :=
  ⟨⟨-7/32, -39/160⟩, 3/320⟩
def center0381 : GaussianRat :=
  ⟨-9885359/62500000, -81782823/500000000⟩
def contact0381 : RatBall := localContactBall tau0381 center0381
def work0381 : RoundedTauEval :=
  evalTau precision tau0381 contact0381 logTwoBall

theorem center_sq0381 : (center0381.re : ℝ)^2 +
    (center0381.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0381]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0381 : work0381.theta.ok = true ∧
    work0381.jac.invOK = true ∧ acceptsUnitSq work0381.out = true := by
  norm_num [work0381, contact0381, tau0381, center0381, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0381 : CellCertificate where
  tauBall := tau0381
  contactCenter := center0381
  contactBall := contact0381
  work := work0381
  center_sq := center_sq0381
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0381.1
  jac_ok := checks0381.2.1
  accepted := checks0381.2.2

def tau0382 : RatBall :=
  ⟨⟨-33/160, -39/160⟩, 3/320⟩
def center0382 : GaussianRat :=
  ⟨-18684153/125000000, -164515579/1000000000⟩
def contact0382 : RatBall := localContactBall tau0382 center0382
def work0382 : RoundedTauEval :=
  evalTau precision tau0382 contact0382 logTwoBall

theorem center_sq0382 : (center0382.re : ℝ)^2 +
    (center0382.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0382]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0382 : work0382.theta.ok = true ∧
    work0382.jac.invOK = true ∧ acceptsUnitSq work0382.out = true := by
  norm_num [work0382, contact0382, tau0382, center0382, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0382 : CellCertificate where
  tauBall := tau0382
  contactCenter := center0382
  contactBall := contact0382
  work := work0382
  center_sq := center_sq0382
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0382.1
  jac_ok := checks0382.2.1
  accepted := checks0382.2.2

def tau0383 : RatBall :=
  ⟨⟨-7/32, -37/160⟩, 3/320⟩
def center0383 : GaussianRat :=
  ⟨-78611951/500000000, -154924327/1000000000⟩
def contact0383 : RatBall := localContactBall tau0383 center0383
def work0383 : RoundedTauEval :=
  evalTau precision tau0383 contact0383 logTwoBall

theorem center_sq0383 : (center0383.re : ℝ)^2 +
    (center0383.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0383]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0383 : work0383.theta.ok = true ∧
    work0383.jac.invOK = true ∧ acceptsUnitSq work0383.out = true := by
  norm_num [work0383, contact0383, tau0383, center0383, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0383 : CellCertificate where
  tauBall := tau0383
  contactCenter := center0383
  contactBall := contact0383
  work := work0383
  center_sq := center_sq0383
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0383.1
  jac_ok := checks0383.2.1
  accepted := checks0383.2.2

def cells : List CellCertificate := [cell0376, cell0377, cell0378, cell0379, cell0380, cell0381, cell0382, cell0383]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047
