import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2216 : RatBall :=
  ⟨⟨-1/64, 121/320⟩, 3/640⟩
def center2216 : GaussianRat :=
  ⟨-254281/20000000, 276265959/1000000000⟩
def contact2216 : RatBall := localContactBall tau2216 center2216
def work2216 : RoundedTauEval :=
  evalTau precision tau2216 contact2216 logTwoBall

theorem center_sq2216 : (center2216.re : ℝ)^2 +
    (center2216.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2216]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2216 : work2216.theta.ok = true ∧
    work2216.jac.invOK = true ∧ acceptsUnitSq work2216.out = true := by
  norm_num [work2216, contact2216, tau2216, center2216, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2216 : CellCertificate where
  tauBall := tau2216
  contactCenter := center2216
  contactBall := contact2216
  work := work2216
  center_sq := center_sq2216
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2216.1
  jac_ok := checks2216.2.1
  accepted := checks2216.2.2

def tau2217 : RatBall :=
  ⟨⟨-7/320, 123/320⟩, 3/640⟩
def center2217 : GaussianRat :=
  ⟨-3580067/200000000, 8789831/31250000⟩
def contact2217 : RatBall := localContactBall tau2217 center2217
def work2217 : RoundedTauEval :=
  evalTau precision tau2217 contact2217 logTwoBall

theorem center_sq2217 : (center2217.re : ℝ)^2 +
    (center2217.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2217]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2217 : work2217.theta.ok = true ∧
    work2217.jac.invOK = true ∧ acceptsUnitSq work2217.out = true := by
  norm_num [work2217, contact2217, tau2217, center2217, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2217 : CellCertificate where
  tauBall := tau2217
  contactCenter := center2217
  contactBall := contact2217
  work := work2217
  center_sq := center_sq2217
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2217.1
  jac_ok := checks2217.2.1
  accepted := checks2217.2.2

def tau2218 : RatBall :=
  ⟨⟨-1/64, 123/320⟩, 3/640⟩
def center2218 : GaussianRat :=
  ⟨-12788043/1000000000, 281364591/1000000000⟩
def contact2218 : RatBall := localContactBall tau2218 center2218
def work2218 : RoundedTauEval :=
  evalTau precision tau2218 contact2218 logTwoBall

theorem center_sq2218 : (center2218.re : ℝ)^2 +
    (center2218.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2218]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2218 : work2218.theta.ok = true ∧
    work2218.jac.invOK = true ∧ acceptsUnitSq work2218.out = true := by
  norm_num [work2218, contact2218, tau2218, center2218, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2218 : CellCertificate where
  tauBall := tau2218
  contactCenter := center2218
  contactBall := contact2218
  work := work2218
  center_sq := center_sq2218
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2218.1
  jac_ok := checks2218.2.1
  accepted := checks2218.2.2

def tau2219 : RatBall :=
  ⟨⟨-3/320, 121/320⟩, 3/640⟩
def center2219 : GaussianRat :=
  ⟨-1907311/250000000, 69081087/250000000⟩
def contact2219 : RatBall := localContactBall tau2219 center2219
def work2219 : RoundedTauEval :=
  evalTau precision tau2219 contact2219 logTwoBall

theorem center_sq2219 : (center2219.re : ℝ)^2 +
    (center2219.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2219]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2219 : work2219.theta.ok = true ∧
    work2219.jac.invOK = true ∧ acceptsUnitSq work2219.out = true := by
  norm_num [work2219, contact2219, tau2219, center2219, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2219 : CellCertificate where
  tauBall := tau2219
  contactCenter := center2219
  contactBall := contact2219
  work := work2219
  center_sq := center_sq2219
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2219.1
  jac_ok := checks2219.2.1
  accepted := checks2219.2.2

def tau2220 : RatBall :=
  ⟨⟨-1/320, 121/320⟩, 3/640⟩
def center2220 : GaussianRat :=
  ⟨-2543217/1000000000, 276353553/1000000000⟩
def contact2220 : RatBall := localContactBall tau2220 center2220
def work2220 : RoundedTauEval :=
  evalTau precision tau2220 contact2220 logTwoBall

theorem center_sq2220 : (center2220.re : ℝ)^2 +
    (center2220.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2220]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2220 : work2220.theta.ok = true ∧
    work2220.jac.invOK = true ∧ acceptsUnitSq work2220.out = true := by
  norm_num [work2220, contact2220, tau2220, center2220, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2220 : CellCertificate where
  tauBall := tau2220
  contactCenter := center2220
  contactBall := contact2220
  work := work2220
  center_sq := center_sq2220
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2220.1
  jac_ok := checks2220.2.1
  accepted := checks2220.2.2

def tau2221 : RatBall :=
  ⟨⟨-3/320, 123/320⟩, 3/640⟩
def center2221 : GaussianRat :=
  ⟨-3836831/500000000, 281424629/1000000000⟩
def contact2221 : RatBall := localContactBall tau2221 center2221
def work2221 : RoundedTauEval :=
  evalTau precision tau2221 contact2221 logTwoBall

theorem center_sq2221 : (center2221.re : ℝ)^2 +
    (center2221.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2221]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2221 : work2221.theta.ok = true ∧
    work2221.jac.invOK = true ∧ acceptsUnitSq work2221.out = true := by
  norm_num [work2221, contact2221, tau2221, center2221, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2221 : CellCertificate where
  tauBall := tau2221
  contactCenter := center2221
  contactBall := contact2221
  work := work2221
  center_sq := center_sq2221
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2221.1
  jac_ok := checks2221.2.1
  accepted := checks2221.2.2

def tau2222 : RatBall :=
  ⟨⟨-1/320, 123/320⟩, 3/640⟩
def center2222 : GaussianRat :=
  ⟨-2558027/1000000000, 14072733/50000000⟩
def contact2222 : RatBall := localContactBall tau2222 center2222
def work2222 : RoundedTauEval :=
  evalTau precision tau2222 contact2222 logTwoBall

theorem center_sq2222 : (center2222.re : ℝ)^2 +
    (center2222.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2222]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2222 : work2222.theta.ok = true ∧
    work2222.jac.invOK = true ∧ acceptsUnitSq work2222.out = true := by
  norm_num [work2222, contact2222, tau2222, center2222, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2222 : CellCertificate where
  tauBall := tau2222
  contactCenter := center2222
  contactBall := contact2222
  work := work2222
  center_sq := center_sq2222
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2222.1
  jac_ok := checks2222.2.1
  accepted := checks2222.2.2

def tau2223 : RatBall :=
  ⟨⟨113/320, 61/320⟩, 3/640⟩
def center2223 : GaussianRat :=
  ⟨242396513/1000000000, 117649273/1000000000⟩
def contact2223 : RatBall := localContactBall tau2223 center2223
def work2223 : RoundedTauEval :=
  evalTau precision tau2223 contact2223 logTwoBall

theorem center_sq2223 : (center2223.re : ℝ)^2 +
    (center2223.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2223]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2223 : work2223.theta.ok = true ∧
    work2223.jac.invOK = true ∧ acceptsUnitSq work2223.out = true := by
  norm_num [work2223, contact2223, tau2223, center2223, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2223 : CellCertificate where
  tauBall := tau2223
  contactCenter := center2223
  contactBall := contact2223
  work := work2223
  center_sq := center_sq2223
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2223.1
  jac_ok := checks2223.2.1
  accepted := checks2223.2.2

def cells : List CellCertificate := [cell2216, cell2217, cell2218, cell2219, cell2220, cell2221, cell2222, cell2223]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277
