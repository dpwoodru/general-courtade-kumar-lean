import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2256 : RatBall :=
  ⟨⟨9/320, 117/320⟩, 3/640⟩
def center2256 : GaussianRat :=
  ⟨4524341/200000000, 53192453/200000000⟩
def contact2256 : RatBall := localContactBall tau2256 center2256
def work2256 : RoundedTauEval :=
  evalTau precision tau2256 contact2256 logTwoBall

theorem center_sq2256 : (center2256.re : ℝ)^2 +
    (center2256.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2256]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2256 : work2256.theta.ok = true ∧
    work2256.jac.invOK = true ∧ acceptsUnitSq work2256.out = true := by
  norm_num [work2256, contact2256, tau2256, center2256, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2256 : CellCertificate where
  tauBall := tau2256
  contactCenter := center2256
  contactBall := contact2256
  work := work2256
  center_sq := center_sq2256
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2256.1
  jac_ok := checks2256.2.1
  accepted := checks2256.2.2

def tau2257 : RatBall :=
  ⟨⟨11/320, 117/320⟩, 3/640⟩
def center2257 : GaussianRat :=
  ⟨863803/31250000, 33228071/125000000⟩
def contact2257 : RatBall := localContactBall tau2257 center2257
def work2257 : RoundedTauEval :=
  evalTau precision tau2257 contact2257 logTwoBall

theorem center_sq2257 : (center2257.re : ℝ)^2 +
    (center2257.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2257]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2257 : work2257.theta.ok = true ∧
    work2257.jac.invOK = true ∧ acceptsUnitSq work2257.out = true := by
  norm_num [work2257, contact2257, tau2257, center2257, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2257 : CellCertificate where
  tauBall := tau2257
  contactCenter := center2257
  contactBall := contact2257
  work := work2257
  center_sq := center_sq2257
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2257.1
  jac_ok := checks2257.2.1
  accepted := checks2257.2.2

def tau2258 : RatBall :=
  ⟨⟨9/320, 119/320⟩, 3/640⟩
def center2258 : GaussianRat :=
  ⟨22747453/1000000000, 270997951/1000000000⟩
def contact2258 : RatBall := localContactBall tau2258 center2258
def work2258 : RoundedTauEval :=
  evalTau precision tau2258 contact2258 logTwoBall

theorem center_sq2258 : (center2258.re : ℝ)^2 +
    (center2258.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2258]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2258 : work2258.theta.ok = true ∧
    work2258.jac.invOK = true ∧ acceptsUnitSq work2258.out = true := by
  norm_num [work2258, contact2258, tau2258, center2258, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2258 : CellCertificate where
  tauBall := tau2258
  contactCenter := center2258
  contactBall := contact2258
  work := work2258
  center_sq := center_sq2258
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2258.1
  jac_ok := checks2258.2.1
  accepted := checks2258.2.2

def tau2259 : RatBall :=
  ⟨⟨11/320, 119/320⟩, 3/640⟩
def center2259 : GaussianRat :=
  ⟨27795199/1000000000, 135428181/500000000⟩
def contact2259 : RatBall := localContactBall tau2259 center2259
def work2259 : RoundedTauEval :=
  evalTau precision tau2259 contact2259 logTwoBall

theorem center_sq2259 : (center2259.re : ℝ)^2 +
    (center2259.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2259]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2259 : work2259.theta.ok = true ∧
    work2259.jac.invOK = true ∧ acceptsUnitSq work2259.out = true := by
  norm_num [work2259, contact2259, tau2259, center2259, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2259 : CellCertificate where
  tauBall := tau2259
  contactCenter := center2259
  contactBall := contact2259
  work := work2259
  center_sq := center_sq2259
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2259.1
  jac_ok := checks2259.2.1
  accepted := checks2259.2.2

def tau2260 : RatBall :=
  ⟨⟨13/320, 117/320⟩, 3/640⟩
def center2260 : GaussianRat :=
  ⟨6531493/200000000, 265659553/1000000000⟩
def contact2260 : RatBall := localContactBall tau2260 center2260
def work2260 : RoundedTauEval :=
  evalTau precision tau2260 contact2260 logTwoBall

theorem center_sq2260 : (center2260.re : ℝ)^2 +
    (center2260.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2260]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2260 : work2260.theta.ok = true ∧
    work2260.jac.invOK = true ∧ acceptsUnitSq work2260.out = true := by
  norm_num [work2260, contact2260, tau2260, center2260, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2260 : CellCertificate where
  tauBall := tau2260
  contactCenter := center2260
  contactBall := contact2260
  work := work2260
  center_sq := center_sq2260
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2260.1
  jac_ok := checks2260.2.1
  accepted := checks2260.2.2

def tau2261 : RatBall :=
  ⟨⟨3/64, 117/320⟩, 3/640⟩
def center2261 : GaussianRat :=
  ⟨18834129/500000000, 13273367/50000000⟩
def contact2261 : RatBall := localContactBall tau2261 center2261
def work2261 : RoundedTauEval :=
  evalTau precision tau2261 contact2261 logTwoBall

theorem center_sq2261 : (center2261.re : ℝ)^2 +
    (center2261.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2261]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2261 : work2261.theta.ok = true ∧
    work2261.jac.invOK = true ∧ acceptsUnitSq work2261.out = true := by
  norm_num [work2261, contact2261, tau2261, center2261, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2261 : CellCertificate where
  tauBall := tau2261
  contactCenter := center2261
  contactBall := contact2261
  work := work2261
  center_sq := center_sq2261
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2261.1
  jac_ok := checks2261.2.1
  accepted := checks2261.2.2

def tau2262 : RatBall :=
  ⟨⟨13/320, 119/320⟩, 3/640⟩
def center2262 : GaussianRat :=
  ⟨32838611/1000000000, 135343343/500000000⟩
def contact2262 : RatBall := localContactBall tau2262 center2262
def work2262 : RoundedTauEval :=
  evalTau precision tau2262 contact2262 logTwoBall

theorem center_sq2262 : (center2262.re : ℝ)^2 +
    (center2262.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2262]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2262 : work2262.theta.ok = true ∧
    work2262.jac.invOK = true ∧ acceptsUnitSq work2262.out = true := by
  norm_num [work2262, contact2262, tau2262, center2262, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2262 : CellCertificate where
  tauBall := tau2262
  contactCenter := center2262
  contactBall := contact2262
  work := work2262
  center_sq := center_sq2262
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2262.1
  jac_ok := checks2262.2.1
  accepted := checks2262.2.2

def tau2263 : RatBall :=
  ⟨⟨3/64, 119/320⟩, 3/640⟩
def center2263 : GaussianRat :=
  ⟨18938457/500000000, 5409781/20000000⟩
def contact2263 : RatBall := localContactBall tau2263 center2263
def work2263 : RoundedTauEval :=
  evalTau precision tau2263 contact2263 logTwoBall

theorem center_sq2263 : (center2263.re : ℝ)^2 +
    (center2263.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2263]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2263 : work2263.theta.ok = true ∧
    work2263.jac.invOK = true ∧ acceptsUnitSq work2263.out = true := by
  norm_num [work2263, contact2263, tau2263, center2263, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2263 : CellCertificate where
  tauBall := tau2263
  contactCenter := center2263
  contactBall := contact2263
  work := work2263
  center_sq := center_sq2263
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2263.1
  jac_ok := checks2263.2.1
  accepted := checks2263.2.2

def cells : List CellCertificate := [cell2256, cell2257, cell2258, cell2259, cell2260, cell2261, cell2262, cell2263]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282
