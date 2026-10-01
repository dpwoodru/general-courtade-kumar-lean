import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2272 : RatBall :=
  ⟨⟨9/320, 121/320⟩, 3/640⟩
def center2272 : GaussianRat :=
  ⟨4575351/200000000, 276061831/1000000000⟩
def contact2272 : RatBall := localContactBall tau2272 center2272
def work2272 : RoundedTauEval :=
  evalTau precision tau2272 contact2272 logTwoBall

theorem center_sq2272 : (center2272.re : ℝ)^2 +
    (center2272.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2272]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2272 : work2272.theta.ok = true ∧
    work2272.jac.invOK = true ∧ acceptsUnitSq work2272.out = true := by
  norm_num [work2272, contact2272, tau2272, center2272, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2272 : CellCertificate where
  tauBall := tau2272
  contactCenter := center2272
  contactBall := contact2272
  work := work2272
  center_sq := center_sq2272
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2272.1
  jac_ok := checks2272.2.1
  accepted := checks2272.2.2

def tau2273 : RatBall :=
  ⟨⟨11/320, 121/320⟩, 3/640⟩
def center2273 : GaussianRat :=
  ⟨27953037/1000000000, 55183249/200000000⟩
def contact2273 : RatBall := localContactBall tau2273 center2273
def work2273 : RoundedTauEval :=
  evalTau precision tau2273 contact2273 logTwoBall

theorem center_sq2273 : (center2273.re : ℝ)^2 +
    (center2273.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2273]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2273 : work2273.theta.ok = true ∧
    work2273.jac.invOK = true ∧ acceptsUnitSq work2273.out = true := by
  norm_num [work2273, contact2273, tau2273, center2273, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2273 : CellCertificate where
  tauBall := tau2273
  contactCenter := center2273
  contactBall := contact2273
  work := work2273
  center_sq := center_sq2273
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2273.1
  jac_ok := checks2273.2.1
  accepted := checks2273.2.2

def tau2274 : RatBall :=
  ⟨⟨9/320, 123/320⟩, 3/640⟩
def center2274 : GaussianRat :=
  ⟨11504853/500000000, 2811547/10000000⟩
def contact2274 : RatBall := localContactBall tau2274 center2274
def work2274 : RoundedTauEval :=
  evalTau precision tau2274 contact2274 logTwoBall

theorem center_sq2274 : (center2274.re : ℝ)^2 +
    (center2274.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2274]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2274 : work2274.theta.ok = true ∧
    work2274.jac.invOK = true ∧ acceptsUnitSq work2274.out = true := by
  norm_num [work2274, contact2274, tau2274, center2274, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2274 : CellCertificate where
  tauBall := tau2274
  contactCenter := center2274
  contactBall := contact2274
  work := work2274
  center_sq := center_sq2274
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2274.1
  jac_ok := checks2274.2.1
  accepted := checks2274.2.2

def tau2275 : RatBall :=
  ⟨⟨13/320, 121/320⟩, 3/640⟩
def center2275 : GaussianRat :=
  ⟨8256217/250000000, 34467723/125000000⟩
def contact2275 : RatBall := localContactBall tau2275 center2275
def work2275 : RoundedTauEval :=
  evalTau precision tau2275 contact2275 logTwoBall

theorem center_sq2275 : (center2275.re : ℝ)^2 +
    (center2275.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2275]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2275 : work2275.theta.ok = true ∧
    work2275.jac.invOK = true ∧ acceptsUnitSq work2275.out = true := by
  norm_num [work2275, contact2275, tau2275, center2275, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2275 : CellCertificate where
  tauBall := tau2275
  contactCenter := center2275
  contactBall := contact2275
  work := work2275
  center_sq := center_sq2275
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2275.1
  jac_ok := checks2275.2.1
  accepted := checks2275.2.2

def tau2276 : RatBall :=
  ⟨⟨3/64, 121/320⟩, 3/640⟩
def center2276 : GaussianRat :=
  ⟨38091451/1000000000, 137769289/500000000⟩
def contact2276 : RatBall := localContactBall tau2276 center2276
def work2276 : RoundedTauEval :=
  evalTau precision tau2276 contact2276 logTwoBall

theorem center_sq2276 : (center2276.re : ℝ)^2 +
    (center2276.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2276]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2276 : work2276.theta.ok = true ∧
    work2276.jac.invOK = true ∧ acceptsUnitSq work2276.out = true := by
  norm_num [work2276, contact2276, tau2276, center2276, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2276 : CellCertificate where
  tauBall := tau2276
  contactCenter := center2276
  contactBall := contact2276
  work := work2276
  center_sq := center_sq2276
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2276.1
  jac_ok := checks2276.2.1
  accepted := checks2276.2.2

def tau2277 : RatBall :=
  ⟨⟨17/320, 113/320⟩, 3/640⟩
def center2277 : GaussianRat :=
  ⟨42220551/1000000000, 25529699/100000000⟩
def contact2277 : RatBall := localContactBall tau2277 center2277
def work2277 : RoundedTauEval :=
  evalTau precision tau2277 contact2277 logTwoBall

theorem center_sq2277 : (center2277.re : ℝ)^2 +
    (center2277.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2277]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2277 : work2277.theta.ok = true ∧
    work2277.jac.invOK = true ∧ acceptsUnitSq work2277.out = true := by
  norm_num [work2277, contact2277, tau2277, center2277, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2277 : CellCertificate where
  tauBall := tau2277
  contactCenter := center2277
  contactBall := contact2277
  work := work2277
  center_sq := center_sq2277
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2277.1
  jac_ok := checks2277.2.1
  accepted := checks2277.2.2

def tau2278 : RatBall :=
  ⟨⟨19/320, 113/320⟩, 3/640⟩
def center2278 : GaussianRat :=
  ⟨47166967/1000000000, 255064157/1000000000⟩
def contact2278 : RatBall := localContactBall tau2278 center2278
def work2278 : RoundedTauEval :=
  evalTau precision tau2278 contact2278 logTwoBall

theorem center_sq2278 : (center2278.re : ℝ)^2 +
    (center2278.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2278]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2278 : work2278.theta.ok = true ∧
    work2278.jac.invOK = true ∧ acceptsUnitSq work2278.out = true := by
  norm_num [work2278, contact2278, tau2278, center2278, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2278 : CellCertificate where
  tauBall := tau2278
  contactCenter := center2278
  contactBall := contact2278
  work := work2278
  center_sq := center_sq2278
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2278.1
  jac_ok := checks2278.2.1
  accepted := checks2278.2.2

def tau2279 : RatBall :=
  ⟨⟨17/320, 23/64⟩, 3/640⟩
def center2279 : GaussianRat :=
  ⟨5305473/125000000, 65064861/250000000⟩
def contact2279 : RatBall := localContactBall tau2279 center2279
def work2279 : RoundedTauEval :=
  evalTau precision tau2279 contact2279 logTwoBall

theorem center_sq2279 : (center2279.re : ℝ)^2 +
    (center2279.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2279]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2279 : work2279.theta.ok = true ∧
    work2279.jac.invOK = true ∧ acceptsUnitSq work2279.out = true := by
  norm_num [work2279, contact2279, tau2279, center2279, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2279 : CellCertificate where
  tauBall := tau2279
  contactCenter := center2279
  contactBall := contact2279
  work := work2279
  center_sq := center_sq2279
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2279.1
  jac_ok := checks2279.2.1
  accepted := checks2279.2.2

def cells : List CellCertificate := [cell2272, cell2273, cell2274, cell2275, cell2276, cell2277, cell2278, cell2279]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284
