import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2360 : RatBall :=
  ⟨⟨57/320, 101/320⟩, 3/640⟩
def center2360 : GaussianRat :=
  ⟨135347471/1000000000, 43651451/200000000⟩
def contact2360 : RatBall := localContactBall tau2360 center2360
def work2360 : RoundedTauEval :=
  evalTau precision tau2360 contact2360 logTwoBall

theorem center_sq2360 : (center2360.re : ℝ)^2 +
    (center2360.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2360]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2360 : work2360.theta.ok = true ∧
    work2360.jac.invOK = true ∧ acceptsUnitSq work2360.out = true := by
  norm_num [work2360, contact2360, tau2360, center2360, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2360 : CellCertificate where
  tauBall := tau2360
  contactCenter := center2360
  contactBall := contact2360
  work := work2360
  center_sq := center_sq2360
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2360.1
  jac_ok := checks2360.2.1
  accepted := checks2360.2.2

def tau2361 : RatBall :=
  ⟨⟨59/320, 101/320⟩, 3/640⟩
def center2361 : GaussianRat :=
  ⟨27985801/200000000, 54418229/250000000⟩
def contact2361 : RatBall := localContactBall tau2361 center2361
def work2361 : RoundedTauEval :=
  evalTau precision tau2361 contact2361 logTwoBall

theorem center_sq2361 : (center2361.re : ℝ)^2 +
    (center2361.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2361]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2361 : work2361.theta.ok = true ∧
    work2361.jac.invOK = true ∧ acceptsUnitSq work2361.out = true := by
  norm_num [work2361, contact2361, tau2361, center2361, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2361 : CellCertificate where
  tauBall := tau2361
  contactCenter := center2361
  contactBall := contact2361
  work := work2361
  center_sq := center_sq2361
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2361.1
  jac_ok := checks2361.2.1
  accepted := checks2361.2.2

def tau2362 : RatBall :=
  ⟨⟨57/320, 103/320⟩, 3/640⟩
def center2362 : GaussianRat :=
  ⟨135931497/1000000000, 55713833/250000000⟩
def contact2362 : RatBall := localContactBall tau2362 center2362
def work2362 : RoundedTauEval :=
  evalTau precision tau2362 contact2362 logTwoBall

theorem center_sq2362 : (center2362.re : ℝ)^2 +
    (center2362.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2362]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2362 : work2362.theta.ok = true ∧
    work2362.jac.invOK = true ∧ acceptsUnitSq work2362.out = true := by
  norm_num [work2362, contact2362, tau2362, center2362, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2362 : CellCertificate where
  tauBall := tau2362
  contactCenter := center2362
  contactBall := contact2362
  work := work2362
  center_sq := center_sq2362
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2362.1
  jac_ok := checks2362.2.1
  accepted := checks2362.2.2

def tau2363 : RatBall :=
  ⟨⟨59/320, 103/320⟩, 3/640⟩
def center2363 : GaussianRat :=
  ⟨140529903/1000000000, 222254637/1000000000⟩
def contact2363 : RatBall := localContactBall tau2363 center2363
def work2363 : RoundedTauEval :=
  evalTau precision tau2363 contact2363 logTwoBall

theorem center_sq2363 : (center2363.re : ℝ)^2 +
    (center2363.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2363]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2363 : work2363.theta.ok = true ∧
    work2363.jac.invOK = true ∧ acceptsUnitSq work2363.out = true := by
  norm_num [work2363, contact2363, tau2363, center2363, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2363 : CellCertificate where
  tauBall := tau2363
  contactCenter := center2363
  contactBall := contact2363
  work := work2363
  center_sq := center_sq2363
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2363.1
  jac_ok := checks2363.2.1
  accepted := checks2363.2.2

def tau2364 : RatBall :=
  ⟨⟨61/320, 101/320⟩, 3/640⟩
def center2364 : GaussianRat :=
  ⟨7224707/50000000, 217072079/1000000000⟩
def contact2364 : RatBall := localContactBall tau2364 center2364
def work2364 : RoundedTauEval :=
  evalTau precision tau2364 contact2364 logTwoBall

theorem center_sq2364 : (center2364.re : ℝ)^2 +
    (center2364.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2364]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2364 : work2364.theta.ok = true ∧
    work2364.jac.invOK = true ∧ acceptsUnitSq work2364.out = true := by
  norm_num [work2364, contact2364, tau2364, center2364, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2364 : CellCertificate where
  tauBall := tau2364
  contactCenter := center2364
  contactBall := contact2364
  work := work2364
  center_sq := center_sq2364
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2364.1
  jac_ok := checks2364.2.1
  accepted := checks2364.2.2

def tau2365 : RatBall :=
  ⟨⟨63/320, 101/320⟩, 3/640⟩
def center2365 : GaussianRat :=
  ⟨74521233/500000000, 108227539/500000000⟩
def contact2365 : RatBall := localContactBall tau2365 center2365
def work2365 : RoundedTauEval :=
  evalTau precision tau2365 contact2365 logTwoBall

theorem center_sq2365 : (center2365.re : ℝ)^2 +
    (center2365.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2365]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2365 : work2365.theta.ok = true ∧
    work2365.jac.invOK = true ∧ acceptsUnitSq work2365.out = true := by
  norm_num [work2365, contact2365, tau2365, center2365, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2365 : CellCertificate where
  tauBall := tau2365
  contactCenter := center2365
  contactBall := contact2365
  work := work2365
  center_sq := center_sq2365
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2365.1
  jac_ok := checks2365.2.1
  accepted := checks2365.2.2

def tau2366 : RatBall :=
  ⟨⟨61/320, 103/320⟩, 3/640⟩
def center2366 : GaussianRat :=
  ⟨5804463/40000000, 221637027/1000000000⟩
def contact2366 : RatBall := localContactBall tau2366 center2366
def work2366 : RoundedTauEval :=
  evalTau precision tau2366 contact2366 logTwoBall

theorem center_sq2366 : (center2366.re : ℝ)^2 +
    (center2366.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2366]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2366 : work2366.theta.ok = true ∧
    work2366.jac.invOK = true ∧ acceptsUnitSq work2366.out = true := by
  norm_num [work2366, contact2366, tau2366, center2366, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2366 : CellCertificate where
  tauBall := tau2366
  contactCenter := center2366
  contactBall := contact2366
  work := work2366
  center_sq := center_sq2366
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2366.1
  jac_ok := checks2366.2.1
  accepted := checks2366.2.2

def tau2367 : RatBall :=
  ⟨⟨63/320, 103/320⟩, 3/640⟩
def center2367 : GaussianRat :=
  ⟨74838049/500000000, 221002847/1000000000⟩
def contact2367 : RatBall := localContactBall tau2367 center2367
def work2367 : RoundedTauEval :=
  evalTau precision tau2367 contact2367 logTwoBall

theorem center_sq2367 : (center2367.re : ℝ)^2 +
    (center2367.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2367]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2367 : work2367.theta.ok = true ∧
    work2367.jac.invOK = true ∧ acceptsUnitSq work2367.out = true := by
  norm_num [work2367, contact2367, tau2367, center2367, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2367 : CellCertificate where
  tauBall := tau2367
  contactCenter := center2367
  contactBall := contact2367
  work := work2367
  center_sq := center_sq2367
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2367.1
  jac_ok := checks2367.2.1
  accepted := checks2367.2.2

def cells : List CellCertificate := [cell2360, cell2361, cell2362, cell2363, cell2364, cell2365, cell2366, cell2367]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295
