import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2352 : RatBall :=
  ⟨⟨57/320, 97/320⟩, 3/640⟩
def center2352 : GaussianRat :=
  ⟨67113521/500000000, 52277787/250000000⟩
def contact2352 : RatBall := localContactBall tau2352 center2352
def work2352 : RoundedTauEval :=
  evalTau precision tau2352 contact2352 logTwoBall

theorem center_sq2352 : (center2352.re : ℝ)^2 +
    (center2352.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2352]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2352 : work2352.theta.ok = true ∧
    work2352.jac.invOK = true ∧ acceptsUnitSq work2352.out = true := by
  norm_num [work2352, contact2352, tau2352, center2352, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2352 : CellCertificate where
  tauBall := tau2352
  contactCenter := center2352
  contactBall := contact2352
  work := work2352
  center_sq := center_sq2352
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2352.1
  jac_ok := checks2352.2.1
  accepted := checks2352.2.2

def tau2353 : RatBall :=
  ⟨⟨59/320, 97/320⟩, 3/640⟩
def center2353 : GaussianRat :=
  ⟨13877609/100000000, 208558553/1000000000⟩
def contact2353 : RatBall := localContactBall tau2353 center2353
def work2353 : RoundedTauEval :=
  evalTau precision tau2353 contact2353 logTwoBall

theorem center_sq2353 : (center2353.re : ℝ)^2 +
    (center2353.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2353]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2353 : work2353.theta.ok = true ∧
    work2353.jac.invOK = true ∧ acceptsUnitSq work2353.out = true := by
  norm_num [work2353, contact2353, tau2353, center2353, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2353 : CellCertificate where
  tauBall := tau2353
  contactCenter := center2353
  contactBall := contact2353
  work := work2353
  center_sq := center_sq2353
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2353.1
  jac_ok := checks2353.2.1
  accepted := checks2353.2.2

def tau2354 : RatBall :=
  ⟨⟨57/320, 99/320⟩, 3/640⟩
def center2354 : GaussianRat :=
  ⟨5391177/40000000, 106838001/500000000⟩
def contact2354 : RatBall := localContactBall tau2354 center2354
def work2354 : RoundedTauEval :=
  evalTau precision tau2354 contact2354 logTwoBall

theorem center_sq2354 : (center2354.re : ℝ)^2 +
    (center2354.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2354]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2354 : work2354.theta.ok = true ∧
    work2354.jac.invOK = true ∧ acceptsUnitSq work2354.out = true := by
  norm_num [work2354, contact2354, tau2354, center2354, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2354 : CellCertificate where
  tauBall := tau2354
  contactCenter := center2354
  contactBall := contact2354
  work := work2354
  center_sq := center_sq2354
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2354.1
  jac_ok := checks2354.2.1
  accepted := checks2354.2.2

def tau2355 : RatBall :=
  ⟨⟨59/320, 99/320⟩, 3/640⟩
def center2355 : GaussianRat :=
  ⟨34836127/250000000, 53276923/250000000⟩
def contact2355 : RatBall := localContactBall tau2355 center2355
def work2355 : RoundedTauEval :=
  evalTau precision tau2355 contact2355 logTwoBall

theorem center_sq2355 : (center2355.re : ℝ)^2 +
    (center2355.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2355]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2355 : work2355.theta.ok = true ∧
    work2355.jac.invOK = true ∧ acceptsUnitSq work2355.out = true := by
  norm_num [work2355, contact2355, tau2355, center2355, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2355 : CellCertificate where
  tauBall := tau2355
  contactCenter := center2355
  contactBall := contact2355
  work := work2355
  center_sq := center_sq2355
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2355.1
  jac_ok := checks2355.2.1
  accepted := checks2355.2.2

def tau2356 : RatBall :=
  ⟨⟨61/320, 97/320⟩, 3/640⟩
def center2356 : GaussianRat :=
  ⟨143309371/1000000000, 103995141/500000000⟩
def contact2356 : RatBall := localContactBall tau2356 center2356
def work2356 : RoundedTauEval :=
  evalTau precision tau2356 contact2356 logTwoBall

theorem center_sq2356 : (center2356.re : ℝ)^2 +
    (center2356.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2356]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2356 : work2356.theta.ok = true ∧
    work2356.jac.invOK = true ∧ acceptsUnitSq work2356.out = true := by
  norm_num [work2356, contact2356, tau2356, center2356, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2356 : CellCertificate where
  tauBall := tau2356
  contactCenter := center2356
  contactBall := contact2356
  work := work2356
  center_sq := center_sq2356
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2356.1
  jac_ok := checks2356.2.1
  accepted := checks2356.2.2

def tau2357 : RatBall :=
  ⟨⟨63/320, 97/320⟩, 3/640⟩
def center2357 : GaussianRat :=
  ⟨147826489/1000000000, 2592583/12500000⟩
def contact2357 : RatBall := localContactBall tau2357 center2357
def work2357 : RoundedTauEval :=
  evalTau precision tau2357 contact2357 logTwoBall

theorem center_sq2357 : (center2357.re : ℝ)^2 +
    (center2357.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2357]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2357 : work2357.theta.ok = true ∧
    work2357.jac.invOK = true ∧ acceptsUnitSq work2357.out = true := by
  norm_num [work2357, contact2357, tau2357, center2357, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2357 : CellCertificate where
  tauBall := tau2357
  contactCenter := center2357
  contactBall := contact2357
  work := work2357
  center_sq := center_sq2357
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2357.1
  jac_ok := checks2357.2.1
  accepted := checks2357.2.2

def tau2358 : RatBall :=
  ⟨⟨61/320, 99/320⟩, 3/640⟩
def center2358 : GaussianRat :=
  ⟨28778703/200000000, 106261649/500000000⟩
def contact2358 : RatBall := localContactBall tau2358 center2358
def work2358 : RoundedTauEval :=
  evalTau precision tau2358 contact2358 logTwoBall

theorem center_sq2358 : (center2358.re : ℝ)^2 +
    (center2358.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2358]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2358 : work2358.theta.ok = true ∧
    work2358.jac.invOK = true ∧ acceptsUnitSq work2358.out = true := by
  norm_num [work2358, contact2358, tau2358, center2358, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2358 : CellCertificate where
  tauBall := tau2358
  contactCenter := center2358
  contactBall := contact2358
  work := work2358
  center_sq := center_sq2358
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2358.1
  jac_ok := checks2358.2.1
  accepted := checks2358.2.2

def tau2359 : RatBall :=
  ⟨⟨63/320, 99/320⟩, 3/640⟩
def center2359 : GaussianRat :=
  ⟨148426041/1000000000, 105961569/500000000⟩
def contact2359 : RatBall := localContactBall tau2359 center2359
def work2359 : RoundedTauEval :=
  evalTau precision tau2359 contact2359 logTwoBall

theorem center_sq2359 : (center2359.re : ℝ)^2 +
    (center2359.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2359]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2359 : work2359.theta.ok = true ∧
    work2359.jac.invOK = true ∧ acceptsUnitSq work2359.out = true := by
  norm_num [work2359, contact2359, tau2359, center2359, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2359 : CellCertificate where
  tauBall := tau2359
  contactCenter := center2359
  contactBall := contact2359
  work := work2359
  center_sq := center_sq2359
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2359.1
  jac_ok := checks2359.2.1
  accepted := checks2359.2.2

def cells : List CellCertificate := [cell2352, cell2353, cell2354, cell2355, cell2356, cell2357, cell2358, cell2359]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294
