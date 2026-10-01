import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0296 : RatBall :=
  ⟨⟨23/80, 1/16⟩, 3/160⟩
def center0296 : GaussianRat :=
  ⟨194534387/1000000000, 7984577/200000000⟩
def contact0296 : RatBall := localContactBall tau0296 center0296
def work0296 : RoundedTauEval :=
  evalTau precision tau0296 contact0296 logTwoBall

theorem center_sq0296 : (center0296.re : ℝ)^2 +
    (center0296.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0296]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0296 : work0296.theta.ok = true ∧
    work0296.jac.invOK = true ∧ acceptsUnitSq work0296.out = true := by
  norm_num [work0296, contact0296, tau0296, center0296, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0296 : CellCertificate where
  tauBall := tau0296
  contactCenter := center0296
  contactBall := contact0296
  work := work0296
  center_sq := center_sq0296
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0296.1
  jac_ok := checks0296.2.1
  accepted := checks0296.2.2

def tau0297 : RatBall :=
  ⟨⟨21/80, 7/80⟩, 3/160⟩
def center0297 : GaussianRat :=
  ⟨17905297/100000000, 5669463/100000000⟩
def contact0297 : RatBall := localContactBall tau0297 center0297
def work0297 : RoundedTauEval :=
  evalTau precision tau0297 contact0297 logTwoBall

theorem center_sq0297 : (center0297.re : ℝ)^2 +
    (center0297.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0297]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0297 : work0297.theta.ok = true ∧
    work0297.jac.invOK = true ∧ acceptsUnitSq work0297.out = true := by
  norm_num [work0297, contact0297, tau0297, center0297, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0297 : CellCertificate where
  tauBall := tau0297
  contactCenter := center0297
  contactBall := contact0297
  work := work0297
  center_sq := center_sq0297
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0297.1
  jac_ok := checks0297.2.1
  accepted := checks0297.2.2

def tau0298 : RatBall :=
  ⟨⟨23/80, 7/80⟩, 3/160⟩
def center0298 : GaussianRat :=
  ⟨195201217/1000000000, 13984569/250000000⟩
def contact0298 : RatBall := localContactBall tau0298 center0298
def work0298 : RoundedTauEval :=
  evalTau precision tau0298 contact0298 logTwoBall

theorem center_sq0298 : (center0298.re : ℝ)^2 +
    (center0298.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0298]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0298 : work0298.theta.ok = true ∧
    work0298.jac.invOK = true ∧ acceptsUnitSq work0298.out = true := by
  norm_num [work0298, contact0298, tau0298, center0298, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0298 : CellCertificate where
  tauBall := tau0298
  contactCenter := center0298
  contactBall := contact0298
  work := work0298
  center_sq := center_sq0298
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0298.1
  jac_ok := checks0298.2.1
  accepted := checks0298.2.2

def tau0299 : RatBall :=
  ⟨⟨5/16, 1/80⟩, 3/160⟩
def center0299 : GaussianRat :=
  ⟨104858117/500000000, 3932321/500000000⟩
def contact0299 : RatBall := localContactBall tau0299 center0299
def work0299 : RoundedTauEval :=
  evalTau precision tau0299 contact0299 logTwoBall

theorem center_sq0299 : (center0299.re : ℝ)^2 +
    (center0299.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0299]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0299 : work0299.theta.ok = true ∧
    work0299.jac.invOK = true ∧ acceptsUnitSq work0299.out = true := by
  norm_num [work0299, contact0299, tau0299, center0299, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0299 : CellCertificate where
  tauBall := tau0299
  contactCenter := center0299
  contactBall := contact0299
  work := work0299
  center_sq := center_sq0299
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0299.1
  jac_ok := checks0299.2.1
  accepted := checks0299.2.2

def tau0300 : RatBall :=
  ⟨⟨27/80, 1/80⟩, 3/160⟩
def center0300 : GaussianRat :=
  ⟨45065623/200000000, 7745371/1000000000⟩
def contact0300 : RatBall := localContactBall tau0300 center0300
def work0300 : RoundedTauEval :=
  evalTau precision tau0300 contact0300 logTwoBall

theorem center_sq0300 : (center0300.re : ℝ)^2 +
    (center0300.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0300]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0300 : work0300.theta.ok = true ∧
    work0300.jac.invOK = true ∧ acceptsUnitSq work0300.out = true := by
  norm_num [work0300, contact0300, tau0300, center0300, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0300 : CellCertificate where
  tauBall := tau0300
  contactCenter := center0300
  contactBall := contact0300
  work := work0300
  center_sq := center_sq0300
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0300.1
  jac_ok := checks0300.2.1
  accepted := checks0300.2.2

def tau0301 : RatBall :=
  ⟨⟨5/16, 3/80⟩, 3/160⟩
def center0301 : GaussianRat :=
  ⟨209949283/1000000000, 11799931/500000000⟩
def contact0301 : RatBall := localContactBall tau0301 center0301
def work0301 : RoundedTauEval :=
  evalTau precision tau0301 contact0301 logTwoBall

theorem center_sq0301 : (center0301.re : ℝ)^2 +
    (center0301.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0301]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0301 : work0301.theta.ok = true ∧
    work0301.jac.invOK = true ∧ acceptsUnitSq work0301.out = true := by
  norm_num [work0301, contact0301, tau0301, center0301, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0301 : CellCertificate where
  tauBall := tau0301
  contactCenter := center0301
  contactBall := contact0301
  work := work0301
  center_sq := center_sq0301
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0301.1
  jac_ok := checks0301.2.1
  accepted := checks0301.2.2

def tau0302 : RatBall :=
  ⟨⟨27/80, 3/80⟩, 3/160⟩
def center0302 : GaussianRat :=
  ⟨225572371/1000000000, 4648277/200000000⟩
def contact0302 : RatBall := localContactBall tau0302 center0302
def work0302 : RoundedTauEval :=
  evalTau precision tau0302 contact0302 logTwoBall

theorem center_sq0302 : (center0302.re : ℝ)^2 +
    (center0302.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0302]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0302 : work0302.theta.ok = true ∧
    work0302.jac.invOK = true ∧ acceptsUnitSq work0302.out = true := by
  norm_num [work0302, contact0302, tau0302, center0302, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0302 : CellCertificate where
  tauBall := tau0302
  contactCenter := center0302
  contactBall := contact0302
  work := work0302
  center_sq := center_sq0302
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0302.1
  jac_ok := checks0302.2.1
  accepted := checks0302.2.2

def tau0303 : RatBall :=
  ⟨⟨29/80, 1/80⟩, 3/160⟩
def center0303 : GaussianRat :=
  ⟨240695961/1000000000, 1905207/250000000⟩
def contact0303 : RatBall := localContactBall tau0303 center0303
def work0303 : RoundedTauEval :=
  evalTau precision tau0303 contact0303 logTwoBall

theorem center_sq0303 : (center0303.re : ℝ)^2 +
    (center0303.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0303]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0303 : work0303.theta.ok = true ∧
    work0303.jac.invOK = true ∧ acceptsUnitSq work0303.out = true := by
  norm_num [work0303, contact0303, tau0303, center0303, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0303 : CellCertificate where
  tauBall := tau0303
  contactCenter := center0303
  contactBall := contact0303
  work := work0303
  center_sq := center_sq0303
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0303.1
  jac_ok := checks0303.2.1
  accepted := checks0303.2.2

def cells : List CellCertificate := [cell0296, cell0297, cell0298, cell0299, cell0300, cell0301, cell0302, cell0303]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037
