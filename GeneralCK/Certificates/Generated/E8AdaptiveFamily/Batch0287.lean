import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2296 : RatBall :=
  ⟨⟨27/320, 23/64⟩, 3/640⟩
def center2296 : GaussianRat :=
  ⟨67227179/1000000000, 258804339/1000000000⟩
def contact2296 : RatBall := localContactBall tau2296 center2296
def work2296 : RoundedTauEval :=
  evalTau precision tau2296 contact2296 logTwoBall

theorem center_sq2296 : (center2296.re : ℝ)^2 +
    (center2296.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2296]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2296 : work2296.theta.ok = true ∧
    work2296.jac.invOK = true ∧ acceptsUnitSq work2296.out = true := by
  norm_num [work2296, contact2296, tau2296, center2296, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2296 : CellCertificate where
  tauBall := tau2296
  contactCenter := center2296
  contactBall := contact2296
  work := work2296
  center_sq := center_sq2296
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2296.1
  jac_ok := checks2296.2.1
  accepted := checks2296.2.2

def tau2297 : RatBall :=
  ⟨⟨29/320, 113/320⟩, 3/640⟩
def center2297 : GaussianRat :=
  ⟨1794563/25000000, 253524459/1000000000⟩
def contact2297 : RatBall := localContactBall tau2297 center2297
def work2297 : RoundedTauEval :=
  evalTau precision tau2297 contact2297 logTwoBall

theorem center_sq2297 : (center2297.re : ℝ)^2 +
    (center2297.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2297]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2297 : work2297.theta.ok = true ∧
    work2297.jac.invOK = true ∧ acceptsUnitSq work2297.out = true := by
  norm_num [work2297, contact2297, tau2297, center2297, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2297 : CellCertificate where
  tauBall := tau2297
  contactCenter := center2297
  contactBall := contact2297
  work := work2297
  center_sq := center_sq2297
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2297.1
  jac_ok := checks2297.2.1
  accepted := checks2297.2.2

def tau2298 : RatBall :=
  ⟨⟨31/320, 113/320⟩, 3/640⟩
def center2298 : GaussianRat :=
  ⟨15335517/200000000, 253142899/1000000000⟩
def contact2298 : RatBall := localContactBall tau2298 center2298
def work2298 : RoundedTauEval :=
  evalTau precision tau2298 contact2298 logTwoBall

theorem center_sq2298 : (center2298.re : ℝ)^2 +
    (center2298.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2298]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2298 : work2298.theta.ok = true ∧
    work2298.jac.invOK = true ∧ acceptsUnitSq work2298.out = true := by
  norm_num [work2298, contact2298, tau2298, center2298, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2298 : CellCertificate where
  tauBall := tau2298
  contactCenter := center2298
  contactBall := contact2298
  work := work2298
  center_sq := center_sq2298
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2298.1
  jac_ok := checks2298.2.1
  accepted := checks2298.2.2

def tau2299 : RatBall :=
  ⟨⟨29/320, 23/64⟩, 3/640⟩
def center2299 : GaussianRat :=
  ⟨4509823/62500000, 258436977/1000000000⟩
def contact2299 : RatBall := localContactBall tau2299 center2299
def work2299 : RoundedTauEval :=
  evalTau precision tau2299 contact2299 logTwoBall

theorem center_sq2299 : (center2299.re : ℝ)^2 +
    (center2299.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2299]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2299 : work2299.theta.ok = true ∧
    work2299.jac.invOK = true ∧ acceptsUnitSq work2299.out = true := by
  norm_num [work2299, contact2299, tau2299, center2299, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2299 : CellCertificate where
  tauBall := tau2299
  contactCenter := center2299
  contactBall := contact2299
  work := work2299
  center_sq := center_sq2299
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2299.1
  jac_ok := checks2299.2.1
  accepted := checks2299.2.2

def tau2300 : RatBall :=
  ⟨⟨31/320, 23/64⟩, 3/640⟩
def center2300 : GaussianRat :=
  ⟨77076663/1000000000, 258044723/1000000000⟩
def contact2300 : RatBall := localContactBall tau2300 center2300
def work2300 : RoundedTauEval :=
  evalTau precision tau2300 contact2300 logTwoBall

theorem center_sq2300 : (center2300.re : ℝ)^2 +
    (center2300.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2300]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2300 : work2300.theta.ok = true ∧
    work2300.jac.invOK = true ∧ acceptsUnitSq work2300.out = true := by
  norm_num [work2300, contact2300, tau2300, center2300, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2300 : CellCertificate where
  tauBall := tau2300
  contactCenter := center2300
  contactBall := contact2300
  work := work2300
  center_sq := center_sq2300
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2300.1
  jac_ok := checks2300.2.1
  accepted := checks2300.2.2

def tau2301 : RatBall :=
  ⟨⟨5/64, 117/320⟩, 3/640⟩
def center2301 : GaussianRat :=
  ⟨3131077/50000000, 66025963/250000000⟩
def contact2301 : RatBall := localContactBall tau2301 center2301
def work2301 : RoundedTauEval :=
  evalTau precision tau2301 contact2301 logTwoBall

theorem center_sq2301 : (center2301.re : ℝ)^2 +
    (center2301.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2301]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2301 : work2301.theta.ok = true ∧
    work2301.jac.invOK = true ∧ acceptsUnitSq work2301.out = true := by
  norm_num [work2301, contact2301, tau2301, center2301, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2301 : CellCertificate where
  tauBall := tau2301
  contactCenter := center2301
  contactBall := contact2301
  work := work2301
  center_sq := center_sq2301
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2301.1
  jac_ok := checks2301.2.1
  accepted := checks2301.2.2

def tau2302 : RatBall :=
  ⟨⟨27/320, 117/320⟩, 3/640⟩
def center2302 : GaussianRat :=
  ⟨844837/12500000, 131876019/500000000⟩
def contact2302 : RatBall := localContactBall tau2302 center2302
def work2302 : RoundedTauEval :=
  evalTau precision tau2302 contact2302 logTwoBall

theorem center_sq2302 : (center2302.re : ℝ)^2 +
    (center2302.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2302]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2302 : work2302.theta.ok = true ∧
    work2302.jac.invOK = true ∧ acceptsUnitSq work2302.out = true := by
  norm_num [work2302, contact2302, tau2302, center2302, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2302 : CellCertificate where
  tauBall := tau2302
  contactCenter := center2302
  contactBall := contact2302
  work := work2302
  center_sq := center_sq2302
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2302.1
  jac_ok := checks2302.2.1
  accepted := checks2302.2.2

def tau2303 : RatBall :=
  ⟨⟨5/64, 119/320⟩, 3/640⟩
def center2303 : GaussianRat :=
  ⟨1574127/25000000, 53817447/200000000⟩
def contact2303 : RatBall := localContactBall tau2303 center2303
def work2303 : RoundedTauEval :=
  evalTau precision tau2303 contact2303 logTwoBall

theorem center_sq2303 : (center2303.re : ℝ)^2 +
    (center2303.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2303]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2303 : work2303.theta.ok = true ∧
    work2303.jac.invOK = true ∧ acceptsUnitSq work2303.out = true := by
  norm_num [work2303, contact2303, tau2303, center2303, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2303 : CellCertificate where
  tauBall := tau2303
  contactCenter := center2303
  contactBall := contact2303
  work := work2303
  center_sq := center_sq2303
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2303.1
  jac_ok := checks2303.2.1
  accepted := checks2303.2.2

def cells : List CellCertificate := [cell2296, cell2297, cell2298, cell2299, cell2300, cell2301, cell2302, cell2303]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287
