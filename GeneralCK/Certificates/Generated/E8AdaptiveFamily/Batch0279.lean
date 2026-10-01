import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2232 : RatBall :=
  ⟨⟨29/320, 109/320⟩, 3/640⟩
def center2232 : GaussianRat :=
  ⟨17765923/250000000, 243771477/1000000000⟩
def contact2232 : RatBall := localContactBall tau2232 center2232
def work2232 : RoundedTauEval :=
  evalTau precision tau2232 contact2232 logTwoBall

theorem center_sq2232 : (center2232.re : ℝ)^2 +
    (center2232.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2232]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2232 : work2232.theta.ok = true ∧
    work2232.jac.invOK = true ∧ acceptsUnitSq work2232.out = true := by
  norm_num [work2232, contact2232, tau2232, center2232, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2232 : CellCertificate where
  tauBall := tau2232
  contactCenter := center2232
  contactBall := contact2232
  work := work2232
  center_sq := center_sq2232
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2232.1
  jac_ok := checks2232.2.1
  accepted := checks2232.2.2

def tau2233 : RatBall :=
  ⟨⟨31/320, 109/320⟩, 3/640⟩
def center2233 : GaussianRat :=
  ⟨75911827/1000000000, 121705269/500000000⟩
def contact2233 : RatBall := localContactBall tau2233 center2233
def work2233 : RoundedTauEval :=
  evalTau precision tau2233 contact2233 logTwoBall

theorem center_sq2233 : (center2233.re : ℝ)^2 +
    (center2233.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2233]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2233 : work2233.theta.ok = true ∧
    work2233.jac.invOK = true ∧ acceptsUnitSq work2233.out = true := by
  norm_num [work2233, contact2233, tau2233, center2233, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2233 : CellCertificate where
  tauBall := tau2233
  contactCenter := center2233
  contactBall := contact2233
  work := work2233
  center_sq := center_sq2233
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2233.1
  jac_ok := checks2233.2.1
  accepted := checks2233.2.2

def tau2234 : RatBall :=
  ⟨⟨29/320, 111/320⟩, 3/640⟩
def center2234 : GaussianRat :=
  ⟨7141811/100000000, 9945447/40000000⟩
def contact2234 : RatBall := localContactBall tau2234 center2234
def work2234 : RoundedTauEval :=
  evalTau precision tau2234 contact2234 logTwoBall

theorem center_sq2234 : (center2234.re : ℝ)^2 +
    (center2234.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2234]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2234 : work2234.theta.ok = true ∧
    work2234.jac.invOK = true ∧ acceptsUnitSq work2234.out = true := by
  norm_num [work2234, contact2234, tau2234, center2234, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2234 : CellCertificate where
  tauBall := tau2234
  contactCenter := center2234
  contactBall := contact2234
  work := work2234
  center_sq := center_sq2234
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2234.1
  jac_ok := checks2234.2.1
  accepted := checks2234.2.2

def tau2235 : RatBall :=
  ⟨⟨31/320, 111/320⟩, 3/640⟩
def center2235 : GaussianRat :=
  ⟨76289393/1000000000, 248265049/1000000000⟩
def contact2235 : RatBall := localContactBall tau2235 center2235
def work2235 : RoundedTauEval :=
  evalTau precision tau2235 contact2235 logTwoBall

theorem center_sq2235 : (center2235.re : ℝ)^2 +
    (center2235.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2235]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2235 : work2235.theta.ok = true ∧
    work2235.jac.invOK = true ∧ acceptsUnitSq work2235.out = true := by
  norm_num [work2235, contact2235, tau2235, center2235, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2235 : CellCertificate where
  tauBall := tau2235
  contactCenter := center2235
  contactBall := contact2235
  work := work2235
  center_sq := center_sq2235
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2235.1
  jac_ok := checks2235.2.1
  accepted := checks2235.2.2

def tau2236 : RatBall :=
  ⟨⟨1/64, 113/320⟩, 3/640⟩
def center2236 : GaussianRat :=
  ⟨12437881/1000000000, 3201937/12500000⟩
def contact2236 : RatBall := localContactBall tau2236 center2236
def work2236 : RoundedTauEval :=
  evalTau precision tau2236 contact2236 logTwoBall

theorem center_sq2236 : (center2236.re : ℝ)^2 +
    (center2236.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2236]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2236 : work2236.theta.ok = true ∧
    work2236.jac.invOK = true ∧ acceptsUnitSq work2236.out = true := by
  norm_num [work2236, contact2236, tau2236, center2236, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2236 : CellCertificate where
  tauBall := tau2236
  contactCenter := center2236
  contactBall := contact2236
  work := work2236
  center_sq := center_sq2236
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2236.1
  jac_ok := checks2236.2.1
  accepted := checks2236.2.2

def tau2237 : RatBall :=
  ⟨⟨7/320, 113/320⟩, 3/640⟩
def center2237 : GaussianRat :=
  ⟨17410471/1000000000, 51215337/200000000⟩
def contact2237 : RatBall := localContactBall tau2237 center2237
def work2237 : RoundedTauEval :=
  evalTau precision tau2237 contact2237 logTwoBall

theorem center_sq2237 : (center2237.re : ℝ)^2 +
    (center2237.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2237]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2237 : work2237.theta.ok = true ∧
    work2237.jac.invOK = true ∧ acceptsUnitSq work2237.out = true := by
  norm_num [work2237, contact2237, tau2237, center2237, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2237 : CellCertificate where
  tauBall := tau2237
  contactCenter := center2237
  contactBall := contact2237
  work := work2237
  center_sq := center_sq2237
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2237.1
  jac_ok := checks2237.2.1
  accepted := checks2237.2.2

def tau2238 : RatBall :=
  ⟨⟨1/64, 23/64⟩, 3/640⟩
def center2238 : GaussianRat :=
  ⟨1563007/125000000, 13057087/50000000⟩
def contact2238 : RatBall := localContactBall tau2238 center2238
def work2238 : RoundedTauEval :=
  evalTau precision tau2238 contact2238 logTwoBall

theorem center_sq2238 : (center2238.re : ℝ)^2 +
    (center2238.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2238]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2238 : work2238.theta.ok = true ∧
    work2238.jac.invOK = true ∧ acceptsUnitSq work2238.out = true := by
  norm_num [work2238, contact2238, tau2238, center2238, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2238 : CellCertificate where
  tauBall := tau2238
  contactCenter := center2238
  contactBall := contact2238
  work := work2238
  center_sq := center_sq2238
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2238.1
  jac_ok := checks2238.2.1
  accepted := checks2238.2.2

def tau2239 : RatBall :=
  ⟨⟨7/320, 23/64⟩, 3/640⟩
def center2239 : GaussianRat :=
  ⟨350061/20000000, 130530621/500000000⟩
def contact2239 : RatBall := localContactBall tau2239 center2239
def work2239 : RoundedTauEval :=
  evalTau precision tau2239 contact2239 logTwoBall

theorem center_sq2239 : (center2239.re : ℝ)^2 +
    (center2239.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2239]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2239 : work2239.theta.ok = true ∧
    work2239.jac.invOK = true ∧ acceptsUnitSq work2239.out = true := by
  norm_num [work2239, contact2239, tau2239, center2239, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2239 : CellCertificate where
  tauBall := tau2239
  contactCenter := center2239
  contactBall := contact2239
  work := work2239
  center_sq := center_sq2239
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2239.1
  jac_ok := checks2239.2.1
  accepted := checks2239.2.2

def cells : List CellCertificate := [cell2232, cell2233, cell2234, cell2235, cell2236, cell2237, cell2238, cell2239]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279
