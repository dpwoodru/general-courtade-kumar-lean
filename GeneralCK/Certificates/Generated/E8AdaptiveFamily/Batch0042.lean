import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0336 : RatBall :=
  ⟨⟨1/16, 21/80⟩, 3/160⟩
def center0336 : GaussianRat :=
  ⟨46572457/1000000000, 46409673/250000000⟩
def contact0336 : RatBall := localContactBall tau0336 center0336
def work0336 : RoundedTauEval :=
  evalTau precision tau0336 contact0336 logTwoBall

theorem center_sq0336 : (center0336.re : ℝ)^2 +
    (center0336.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0336]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0336 : work0336.theta.ok = true ∧
    work0336.jac.invOK = true ∧ acceptsUnitSq work0336.out = true := by
  norm_num [work0336, contact0336, tau0336, center0336, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0336 : CellCertificate where
  tauBall := tau0336
  contactCenter := center0336
  contactBall := contact0336
  work := work0336
  center_sq := center_sq0336
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0336.1
  jac_ok := checks0336.2.1
  accepted := checks0336.2.2

def tau0337 : RatBall :=
  ⟨⟨7/80, 21/80⟩, 3/160⟩
def center0337 : GaussianRat :=
  ⟨6508393/100000000, 184829567/1000000000⟩
def contact0337 : RatBall := localContactBall tau0337 center0337
def work0337 : RoundedTauEval :=
  evalTau precision tau0337 contact0337 logTwoBall

theorem center_sq0337 : (center0337.re : ℝ)^2 +
    (center0337.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0337]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0337 : work0337.theta.ok = true ∧
    work0337.jac.invOK = true ∧ acceptsUnitSq work0337.out = true := by
  norm_num [work0337, contact0337, tau0337, center0337, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0337 : CellCertificate where
  tauBall := tau0337
  contactCenter := center0337
  contactBall := contact0337
  work := work0337
  center_sq := center_sq0337
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0337.1
  jac_ok := checks0337.2.1
  accepted := checks0337.2.2

def tau0338 : RatBall :=
  ⟨⟨9/80, 17/80⟩, 3/160⟩
def center0338 : GaussianRat :=
  ⟨4068673/50000000, 73782899/500000000⟩
def contact0338 : RatBall := localContactBall tau0338 center0338
def work0338 : RoundedTauEval :=
  evalTau precision tau0338 contact0338 logTwoBall

theorem center_sq0338 : (center0338.re : ℝ)^2 +
    (center0338.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0338]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0338 : work0338.theta.ok = true ∧
    work0338.jac.invOK = true ∧ acceptsUnitSq work0338.out = true := by
  norm_num [work0338, contact0338, tau0338, center0338, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0338 : CellCertificate where
  tauBall := tau0338
  contactCenter := center0338
  contactBall := contact0338
  work := work0338
  center_sq := center_sq0338
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0338.1
  jac_ok := checks0338.2.1
  accepted := checks0338.2.2

def tau0339 : RatBall :=
  ⟨⟨11/80, 17/80⟩, 3/160⟩
def center0339 : GaussianRat :=
  ⟨24798221/250000000, 36637923/250000000⟩
def contact0339 : RatBall := localContactBall tau0339 center0339
def work0339 : RoundedTauEval :=
  evalTau precision tau0339 contact0339 logTwoBall

theorem center_sq0339 : (center0339.re : ℝ)^2 +
    (center0339.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0339]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0339 : work0339.theta.ok = true ∧
    work0339.jac.invOK = true ∧ acceptsUnitSq work0339.out = true := by
  norm_num [work0339, contact0339, tau0339, center0339, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0339 : CellCertificate where
  tauBall := tau0339
  contactCenter := center0339
  contactBall := contact0339
  work := work0339
  center_sq := center_sq0339
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0339.1
  jac_ok := checks0339.2.1
  accepted := checks0339.2.2

def tau0340 : RatBall :=
  ⟨⟨9/80, 19/80⟩, 3/160⟩
def center0340 : GaussianRat :=
  ⟨20589547/250000000, 33110861/200000000⟩
def contact0340 : RatBall := localContactBall tau0340 center0340
def work0340 : RoundedTauEval :=
  evalTau precision tau0340 contact0340 logTwoBall

theorem center_sq0340 : (center0340.re : ℝ)^2 +
    (center0340.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0340]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0340 : work0340.theta.ok = true ∧
    work0340.jac.invOK = true ∧ acceptsUnitSq work0340.out = true := by
  norm_num [work0340, contact0340, tau0340, center0340, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0340 : CellCertificate where
  tauBall := tau0340
  contactCenter := center0340
  contactBall := contact0340
  work := work0340
  center_sq := center_sq0340
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0340.1
  jac_ok := checks0340.2.1
  accepted := checks0340.2.2

def tau0341 : RatBall :=
  ⟨⟨11/80, 19/80⟩, 3/160⟩
def center0341 : GaussianRat :=
  ⟨25094739/250000000, 82197279/500000000⟩
def contact0341 : RatBall := localContactBall tau0341 center0341
def work0341 : RoundedTauEval :=
  evalTau precision tau0341 contact0341 logTwoBall

theorem center_sq0341 : (center0341.re : ℝ)^2 +
    (center0341.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0341]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0341 : work0341.theta.ok = true ∧
    work0341.jac.invOK = true ∧ acceptsUnitSq work0341.out = true := by
  norm_num [work0341, contact0341, tau0341, center0341, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0341 : CellCertificate where
  tauBall := tau0341
  contactCenter := center0341
  contactBall := contact0341
  work := work0341
  center_sq := center_sq0341
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0341.1
  jac_ok := checks0341.2.1
  accepted := checks0341.2.2

def tau0342 : RatBall :=
  ⟨⟨13/80, 17/80⟩, 3/160⟩
def center0342 : GaussianRat :=
  ⟨58429249/500000000, 145353777/1000000000⟩
def contact0342 : RatBall := localContactBall tau0342 center0342
def work0342 : RoundedTauEval :=
  evalTau precision tau0342 contact0342 logTwoBall

theorem center_sq0342 : (center0342.re : ℝ)^2 +
    (center0342.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0342]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0342 : work0342.theta.ok = true ∧
    work0342.jac.invOK = true ∧ acceptsUnitSq work0342.out = true := by
  norm_num [work0342, contact0342, tau0342, center0342, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0342 : CellCertificate where
  tauBall := tau0342
  contactCenter := center0342
  contactBall := contact0342
  work := work0342
  center_sq := center_sq0342
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0342.1
  jac_ok := checks0342.2.1
  accepted := checks0342.2.2

def tau0343 : RatBall :=
  ⟨⟨3/16, 17/80⟩, 3/160⟩
def center0343 : GaussianRat :=
  ⟨16793263/125000000, 143981719/1000000000⟩
def contact0343 : RatBall := localContactBall tau0343 center0343
def work0343 : RoundedTauEval :=
  evalTau precision tau0343 contact0343 logTwoBall

theorem center_sq0343 : (center0343.re : ℝ)^2 +
    (center0343.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0343]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0343 : work0343.theta.ok = true ∧
    work0343.jac.invOK = true ∧ acceptsUnitSq work0343.out = true := by
  norm_num [work0343, contact0343, tau0343, center0343, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0343 : CellCertificate where
  tauBall := tau0343
  contactCenter := center0343
  contactBall := contact0343
  work := work0343
  center_sq := center_sq0343
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0343.1
  jac_ok := checks0343.2.1
  accepted := checks0343.2.2

def cells : List CellCertificate := [cell0336, cell0337, cell0338, cell0339, cell0340, cell0341, cell0342, cell0343]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042
