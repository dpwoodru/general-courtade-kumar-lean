import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2456 : RatBall :=
  ⟨⟨89/320, 81/320⟩, 3/640⟩
def center2456 : GaussianRat :=
  ⟨199473497/1000000000, 41191221/250000000⟩
def contact2456 : RatBall := localContactBall tau2456 center2456
def work2456 : RoundedTauEval :=
  evalTau precision tau2456 contact2456 logTwoBall

theorem center_sq2456 : (center2456.re : ℝ)^2 +
    (center2456.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2456]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2456 : work2456.theta.ok = true ∧
    work2456.jac.invOK = true ∧ acceptsUnitSq work2456.out = true := by
  norm_num [work2456, contact2456, tau2456, center2456, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2456 : CellCertificate where
  tauBall := tau2456
  contactCenter := center2456
  contactBall := contact2456
  work := work2456
  center_sq := center_sq2456
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2456.1
  jac_ok := checks2456.2.1
  accepted := checks2456.2.2

def tau2457 : RatBall :=
  ⟨⟨91/320, 81/320⟩, 3/640⟩
def center2457 : GaussianRat :=
  ⟨101825843/500000000, 82077687/500000000⟩
def contact2457 : RatBall := localContactBall tau2457 center2457
def work2457 : RoundedTauEval :=
  evalTau precision tau2457 contact2457 logTwoBall

theorem center_sq2457 : (center2457.re : ℝ)^2 +
    (center2457.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2457]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2457 : work2457.theta.ok = true ∧
    work2457.jac.invOK = true ∧ acceptsUnitSq work2457.out = true := by
  norm_num [work2457, contact2457, tau2457, center2457, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2457 : CellCertificate where
  tauBall := tau2457
  contactCenter := center2457
  contactBall := contact2457
  work := work2457
  center_sq := center_sq2457
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2457.1
  jac_ok := checks2457.2.1
  accepted := checks2457.2.2

def tau2458 : RatBall :=
  ⟨⟨89/320, 83/320⟩, 3/640⟩
def center2458 : GaussianRat :=
  ⟨100043853/500000000, 84478333/500000000⟩
def contact2458 : RatBall := localContactBall tau2458 center2458
def work2458 : RoundedTauEval :=
  evalTau precision tau2458 contact2458 logTwoBall

theorem center_sq2458 : (center2458.re : ℝ)^2 +
    (center2458.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2458]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2458 : work2458.theta.ok = true ∧
    work2458.jac.invOK = true ∧ acceptsUnitSq work2458.out = true := by
  norm_num [work2458, contact2458, tau2458, center2458, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2458 : CellCertificate where
  tauBall := tau2458
  contactCenter := center2458
  contactBall := contact2458
  work := work2458
  center_sq := center_sq2458
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2458.1
  jac_ok := checks2458.2.1
  accepted := checks2458.2.2

def tau2459 : RatBall :=
  ⟨⟨91/320, 83/320⟩, 3/640⟩
def center2459 : GaussianRat :=
  ⟨204274783/1000000000, 168328783/1000000000⟩
def contact2459 : RatBall := localContactBall tau2459 center2459
def work2459 : RoundedTauEval :=
  evalTau precision tau2459 contact2459 logTwoBall

theorem center_sq2459 : (center2459.re : ℝ)^2 +
    (center2459.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2459]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2459 : work2459.theta.ok = true ∧
    work2459.jac.invOK = true ∧ acceptsUnitSq work2459.out = true := by
  norm_num [work2459, contact2459, tau2459, center2459, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2459 : CellCertificate where
  tauBall := tau2459
  contactCenter := center2459
  contactBall := contact2459
  work := work2459
  center_sq := center_sq2459
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2459.1
  jac_ok := checks2459.2.1
  accepted := checks2459.2.2

def tau2460 : RatBall :=
  ⟨⟨93/320, 81/320⟩, 3/640⟩
def center2460 : GaussianRat :=
  ⟨103905761/500000000, 163537217/1000000000⟩
def contact2460 : RatBall := localContactBall tau2460 center2460
def work2460 : RoundedTauEval :=
  evalTau precision tau2460 contact2460 logTwoBall

theorem center_sq2460 : (center2460.re : ℝ)^2 +
    (center2460.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2460 : work2460.theta.ok = true ∧
    work2460.jac.invOK = true ∧ acceptsUnitSq work2460.out = true := by
  norm_num [work2460, contact2460, tau2460, center2460, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2460 : CellCertificate where
  tauBall := tau2460
  contactCenter := center2460
  contactBall := contact2460
  work := work2460
  center_sq := center_sq2460
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2460.1
  jac_ok := checks2460.2.1
  accepted := checks2460.2.2

def tau2461 : RatBall :=
  ⟨⟨19/64, 81/320⟩, 3/640⟩
def center2461 : GaussianRat :=
  ⟨211952789/1000000000, 162910673/1000000000⟩
def contact2461 : RatBall := localContactBall tau2461 center2461
def work2461 : RoundedTauEval :=
  evalTau precision tau2461 contact2461 logTwoBall

theorem center_sq2461 : (center2461.re : ℝ)^2 +
    (center2461.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2461]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2461 : work2461.theta.ok = true ∧
    work2461.jac.invOK = true ∧ acceptsUnitSq work2461.out = true := by
  norm_num [work2461, contact2461, tau2461, center2461, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2461 : CellCertificate where
  tauBall := tau2461
  contactCenter := center2461
  contactBall := contact2461
  work := work2461
  center_sq := center_sq2461
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2461.1
  jac_ok := checks2461.2.1
  accepted := checks2461.2.2

def tau2462 : RatBall :=
  ⟨⟨93/320, 83/320⟩, 3/640⟩
def center2462 : GaussianRat :=
  ⟨52110811/250000000, 167692033/1000000000⟩
def contact2462 : RatBall := localContactBall tau2462 center2462
def work2462 : RoundedTauEval :=
  evalTau precision tau2462 contact2462 logTwoBall

theorem center_sq2462 : (center2462.re : ℝ)^2 +
    (center2462.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2462]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2462 : work2462.theta.ok = true ∧
    work2462.jac.invOK = true ∧ acceptsUnitSq work2462.out = true := by
  norm_num [work2462, contact2462, tau2462, center2462, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2462 : CellCertificate where
  tauBall := tau2462
  contactCenter := center2462
  contactBall := contact2462
  work := work2462
  center_sq := center_sq2462
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2462.1
  jac_ok := checks2462.2.1
  accepted := checks2462.2.2

def tau2463 : RatBall :=
  ⟨⟨19/64, 83/320⟩, 3/640⟩
def center2463 : GaussianRat :=
  ⟨212592873/1000000000, 33409337/200000000⟩
def contact2463 : RatBall := localContactBall tau2463 center2463
def work2463 : RoundedTauEval :=
  evalTau precision tau2463 contact2463 logTwoBall

theorem center_sq2463 : (center2463.re : ℝ)^2 +
    (center2463.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2463]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2463 : work2463.theta.ok = true ∧
    work2463.jac.invOK = true ∧ acceptsUnitSq work2463.out = true := by
  norm_num [work2463, contact2463, tau2463, center2463, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2463 : CellCertificate where
  tauBall := tau2463
  contactCenter := center2463
  contactBall := contact2463
  work := work2463
  center_sq := center_sq2463
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2463.1
  jac_ok := checks2463.2.1
  accepted := checks2463.2.2

def cells : List CellCertificate := [cell2456, cell2457, cell2458, cell2459, cell2460, cell2461, cell2462, cell2463]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307
