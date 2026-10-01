import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0384 : RatBall :=
  ⟨⟨-33/160, -37/160⟩, 3/320⟩
def center0384 : GaussianRat :=
  ⟨-148574359/1000000000, -31163137/200000000⟩
def contact0384 : RatBall := localContactBall tau0384 center0384
def work0384 : RoundedTauEval :=
  evalTau precision tau0384 contact0384 logTwoBall

theorem center_sq0384 : (center0384.re : ℝ)^2 +
    (center0384.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0384]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0384 : work0384.theta.ok = true ∧
    work0384.jac.invOK = true ∧ acceptsUnitSq work0384.out = true := by
  norm_num [work0384, contact0384, tau0384, center0384, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0384 : CellCertificate where
  tauBall := tau0384
  contactCenter := center0384
  contactBall := contact0384
  work := work0384
  center_sq := center_sq0384
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0384.1
  jac_ok := checks0384.2.1
  accepted := checks0384.2.2

def tau0385 : RatBall :=
  ⟨⟨-39/160, -7/32⟩, 3/320⟩
def center0385 : GaussianRat :=
  ⟨-173384937/1000000000, -144541281/1000000000⟩
def contact0385 : RatBall := localContactBall tau0385 center0385
def work0385 : RoundedTauEval :=
  evalTau precision tau0385 contact0385 logTwoBall

theorem center_sq0385 : (center0385.re : ℝ)^2 +
    (center0385.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0385]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0385 : work0385.theta.ok = true ∧
    work0385.jac.invOK = true ∧ acceptsUnitSq work0385.out = true := by
  norm_num [work0385, contact0385, tau0385, center0385, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0385 : CellCertificate where
  tauBall := tau0385
  contactCenter := center0385
  contactBall := contact0385
  work := work0385
  center_sq := center_sq0385
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0385.1
  jac_ok := checks0385.2.1
  accepted := checks0385.2.2

def tau0386 : RatBall :=
  ⟨⟨-37/160, -7/32⟩, 3/320⟩
def center0386 : GaussianRat :=
  ⟨-164892819/1000000000, -29090197/200000000⟩
def contact0386 : RatBall := localContactBall tau0386 center0386
def work0386 : RoundedTauEval :=
  evalTau precision tau0386 contact0386 logTwoBall

theorem center_sq0386 : (center0386.re : ℝ)^2 +
    (center0386.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0386]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0386 : work0386.theta.ok = true ∧
    work0386.jac.invOK = true ∧ acceptsUnitSq work0386.out = true := by
  norm_num [work0386, contact0386, tau0386, center0386, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0386 : CellCertificate where
  tauBall := tau0386
  contactCenter := center0386
  contactBall := contact0386
  work := work0386
  center_sq := center_sq0386
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0386.1
  jac_ok := checks0386.2.1
  accepted := checks0386.2.2

def tau0387 : RatBall :=
  ⟨⟨-39/160, -33/160⟩, 3/320⟩
def center0387 : GaussianRat :=
  ⟨-172488051/1000000000, -136096987/1000000000⟩
def contact0387 : RatBall := localContactBall tau0387 center0387
def work0387 : RoundedTauEval :=
  evalTau precision tau0387 contact0387 logTwoBall

theorem center_sq0387 : (center0387.re : ℝ)^2 +
    (center0387.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0387]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0387 : work0387.theta.ok = true ∧
    work0387.jac.invOK = true ∧ acceptsUnitSq work0387.out = true := by
  norm_num [work0387, contact0387, tau0387, center0387, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0387 : CellCertificate where
  tauBall := tau0387
  contactCenter := center0387
  contactBall := contact0387
  work := work0387
  center_sq := center_sq0387
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0387.1
  jac_ok := checks0387.2.1
  accepted := checks0387.2.2

def tau0388 : RatBall :=
  ⟨⟨-37/160, -33/160⟩, 3/320⟩
def center0388 : GaussianRat :=
  ⟨-164030831/1000000000, -3423667/25000000⟩
def contact0388 : RatBall := localContactBall tau0388 center0388
def work0388 : RoundedTauEval :=
  evalTau precision tau0388 contact0388 logTwoBall

theorem center_sq0388 : (center0388.re : ℝ)^2 +
    (center0388.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0388]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0388 : work0388.theta.ok = true ∧
    work0388.jac.invOK = true ∧ acceptsUnitSq work0388.out = true := by
  norm_num [work0388, contact0388, tau0388, center0388, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0388 : CellCertificate where
  tauBall := tau0388
  contactCenter := center0388
  contactBall := contact0388
  work := work0388
  center_sq := center_sq0388
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0388.1
  jac_ok := checks0388.2.1
  accepted := checks0388.2.2

def tau0389 : RatBall :=
  ⟨⟨-7/32, -7/32⟩, 3/320⟩
def center0389 : GaussianRat :=
  ⟨-78170517/500000000, -14632387/100000000⟩
def contact0389 : RatBall := localContactBall tau0389 center0389
def work0389 : RoundedTauEval :=
  evalTau precision tau0389 contact0389 logTwoBall

theorem center_sq0389 : (center0389.re : ℝ)^2 +
    (center0389.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0389]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0389 : work0389.theta.ok = true ∧
    work0389.jac.invOK = true ∧ acceptsUnitSq work0389.out = true := by
  norm_num [work0389, contact0389, tau0389, center0389, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0389 : CellCertificate where
  tauBall := tau0389
  contactCenter := center0389
  contactBall := contact0389
  work := work0389
  center_sq := center_sq0389
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0389.1
  jac_ok := checks0389.2.1
  accepted := checks0389.2.2

def tau0390 : RatBall :=
  ⟨⟨-33/160, -7/32⟩, 3/320⟩
def center0390 : GaussianRat :=
  ⟨-7386597/50000000, -7357917/50000000⟩
def contact0390 : RatBall := localContactBall tau0390 center0390
def work0390 : RoundedTauEval :=
  evalTau precision tau0390 contact0390 logTwoBall

theorem center_sq0390 : (center0390.re : ℝ)^2 +
    (center0390.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0390]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0390 : work0390.theta.ok = true ∧
    work0390.jac.invOK = true ∧ acceptsUnitSq work0390.out = true := by
  norm_num [work0390, contact0390, tau0390, center0390, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0390 : CellCertificate where
  tauBall := tau0390
  contactCenter := center0390
  contactBall := contact0390
  work := work0390
  center_sq := center_sq0390
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0390.1
  jac_ok := checks0390.2.1
  accepted := checks0390.2.2

def tau0391 : RatBall :=
  ⟨⟨-7/32, -33/160⟩, 3/320⟩
def center0391 : GaussianRat :=
  ⟨-31103099/200000000, -137761833/1000000000⟩
def contact0391 : RatBall := localContactBall tau0391 center0391
def work0391 : RoundedTauEval :=
  evalTau precision tau0391 contact0391 logTwoBall

theorem center_sq0391 : (center0391.re : ℝ)^2 +
    (center0391.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0391]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0391 : work0391.theta.ok = true ∧
    work0391.jac.invOK = true ∧ acceptsUnitSq work0391.out = true := by
  norm_num [work0391, contact0391, tau0391, center0391, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0391 : CellCertificate where
  tauBall := tau0391
  contactCenter := center0391
  contactBall := contact0391
  work := work0391
  center_sq := center_sq0391
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0391.1
  jac_ok := checks0391.2.1
  accepted := checks0391.2.2

def cells : List CellCertificate := [cell0384, cell0385, cell0386, cell0387, cell0388, cell0389, cell0390, cell0391]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048
