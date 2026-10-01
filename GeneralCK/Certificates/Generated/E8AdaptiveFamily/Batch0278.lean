import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2224 : RatBall :=
  ⟨⟨21/320, 109/320⟩, 3/640⟩
def center2224 : GaussianRat :=
  ⟨51579953/1000000000, 48996707/200000000⟩
def contact2224 : RatBall := localContactBall tau2224 center2224
def work2224 : RoundedTauEval :=
  evalTau precision tau2224 contact2224 logTwoBall

theorem center_sq2224 : (center2224.re : ℝ)^2 +
    (center2224.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2224 : work2224.theta.ok = true ∧
    work2224.jac.invOK = true ∧ acceptsUnitSq work2224.out = true := by
  norm_num [work2224, contact2224, tau2224, center2224, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2224 : CellCertificate where
  tauBall := tau2224
  contactCenter := center2224
  contactBall := contact2224
  work := work2224
  center_sq := center_sq2224
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2224.1
  jac_ok := checks2224.2.1
  accepted := checks2224.2.2

def tau2225 : RatBall :=
  ⟨⟨23/320, 109/320⟩, 3/640⟩
def center2225 : GaussianRat :=
  ⟨56463291/1000000000, 15294731/62500000⟩
def contact2225 : RatBall := localContactBall tau2225 center2225
def work2225 : RoundedTauEval :=
  evalTau precision tau2225 contact2225 logTwoBall

theorem center_sq2225 : (center2225.re : ℝ)^2 +
    (center2225.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2225]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2225 : work2225.theta.ok = true ∧
    work2225.jac.invOK = true ∧ acceptsUnitSq work2225.out = true := by
  norm_num [work2225, contact2225, tau2225, center2225, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2225 : CellCertificate where
  tauBall := tau2225
  contactCenter := center2225
  contactBall := contact2225
  work := work2225
  center_sq := center_sq2225
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2225.1
  jac_ok := checks2225.2.1
  accepted := checks2225.2.2

def tau2226 : RatBall :=
  ⟨⟨21/320, 111/320⟩, 3/640⟩
def center2226 : GaussianRat :=
  ⟨51839561/1000000000, 31235321/125000000⟩
def contact2226 : RatBall := localContactBall tau2226 center2226
def work2226 : RoundedTauEval :=
  evalTau precision tau2226 contact2226 logTwoBall

theorem center_sq2226 : (center2226.re : ℝ)^2 +
    (center2226.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2226 : work2226.theta.ok = true ∧
    work2226.jac.invOK = true ∧ acceptsUnitSq work2226.out = true := by
  norm_num [work2226, contact2226, tau2226, center2226, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2226 : CellCertificate where
  tauBall := tau2226
  contactCenter := center2226
  contactBall := contact2226
  work := work2226
  center_sq := center_sq2226
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2226.1
  jac_ok := checks2226.2.1
  accepted := checks2226.2.2

def tau2227 : RatBall :=
  ⟨⟨23/320, 111/320⟩, 3/640⟩
def center2227 : GaussianRat :=
  ⟨11349381/200000000, 62401781/250000000⟩
def contact2227 : RatBall := localContactBall tau2227 center2227
def work2227 : RoundedTauEval :=
  evalTau precision tau2227 contact2227 logTwoBall

theorem center_sq2227 : (center2227.re : ℝ)^2 +
    (center2227.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2227]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2227 : work2227.theta.ok = true ∧
    work2227.jac.invOK = true ∧ acceptsUnitSq work2227.out = true := by
  norm_num [work2227, contact2227, tau2227, center2227, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2227 : CellCertificate where
  tauBall := tau2227
  contactCenter := center2227
  contactBall := contact2227
  work := work2227
  center_sq := center_sq2227
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2227.1
  jac_ok := checks2227.2.1
  accepted := checks2227.2.2

def tau2228 : RatBall :=
  ⟨⟨5/64, 109/320⟩, 3/640⟩
def center2228 : GaussianRat :=
  ⟨6133879/100000000, 244424273/1000000000⟩
def contact2228 : RatBall := localContactBall tau2228 center2228
def work2228 : RoundedTauEval :=
  evalTau precision tau2228 contact2228 logTwoBall

theorem center_sq2228 : (center2228.re : ℝ)^2 +
    (center2228.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2228]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2228 : work2228.theta.ok = true ∧
    work2228.jac.invOK = true ∧ acceptsUnitSq work2228.out = true := by
  norm_num [work2228, contact2228, tau2228, center2228, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2228 : CellCertificate where
  tauBall := tau2228
  contactCenter := center2228
  contactBall := contact2228
  work := work2228
  center_sq := center_sq2228
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2228.1
  jac_ok := checks2228.2.1
  accepted := checks2228.2.2

def tau2229 : RatBall :=
  ⟨⟨27/320, 109/320⟩, 3/640⟩
def center2229 : GaussianRat :=
  ⟨16551451/250000000, 30513683/125000000⟩
def contact2229 : RatBall := localContactBall tau2229 center2229
def work2229 : RoundedTauEval :=
  evalTau precision tau2229 contact2229 logTwoBall

theorem center_sq2229 : (center2229.re : ℝ)^2 +
    (center2229.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2229]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2229 : work2229.theta.ok = true ∧
    work2229.jac.invOK = true ∧ acceptsUnitSq work2229.out = true := by
  norm_num [work2229, contact2229, tau2229, center2229, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2229 : CellCertificate where
  tauBall := tau2229
  contactCenter := center2229
  contactBall := contact2229
  work := work2229
  center_sq := center_sq2229
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2229.1
  jac_ok := checks2229.2.1
  accepted := checks2229.2.2

def tau2230 : RatBall :=
  ⟨⟨5/64, 111/320⟩, 3/640⟩
def center2230 : GaussianRat :=
  ⟨30823109/500000000, 249307439/1000000000⟩
def contact2230 : RatBall := localContactBall tau2230 center2230
def work2230 : RoundedTauEval :=
  evalTau precision tau2230 contact2230 logTwoBall

theorem center_sq2230 : (center2230.re : ℝ)^2 +
    (center2230.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2230]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2230 : work2230.theta.ok = true ∧
    work2230.jac.invOK = true ∧ acceptsUnitSq work2230.out = true := by
  norm_num [work2230, contact2230, tau2230, center2230, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2230 : CellCertificate where
  tauBall := tau2230
  contactCenter := center2230
  contactBall := contact2230
  work := work2230
  center_sq := center_sq2230
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2230.1
  jac_ok := checks2230.2.1
  accepted := checks2230.2.2

def tau2231 : RatBall :=
  ⟨⟨27/320, 111/320⟩, 3/640⟩
def center2231 : GaussianRat :=
  ⟨66536837/1000000000, 62245929/250000000⟩
def contact2231 : RatBall := localContactBall tau2231 center2231
def work2231 : RoundedTauEval :=
  evalTau precision tau2231 contact2231 logTwoBall

theorem center_sq2231 : (center2231.re : ℝ)^2 +
    (center2231.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2231]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2231 : work2231.theta.ok = true ∧
    work2231.jac.invOK = true ∧ acceptsUnitSq work2231.out = true := by
  norm_num [work2231, contact2231, tau2231, center2231, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2231 : CellCertificate where
  tauBall := tau2231
  contactCenter := center2231
  contactBall := contact2231
  work := work2231
  center_sq := center_sq2231
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2231.1
  jac_ok := checks2231.2.1
  accepted := checks2231.2.2

def cells : List CellCertificate := [cell2224, cell2225, cell2226, cell2227, cell2228, cell2229, cell2230, cell2231]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278
