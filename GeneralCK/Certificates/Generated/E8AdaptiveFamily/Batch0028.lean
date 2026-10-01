import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0224 : RatBall :=
  ⟨⟨-21/80, 9/80⟩, 3/160⟩
def center0224 : GaussianRat :=
  ⟨-44973153/250000000, 72980409/1000000000⟩
def contact0224 : RatBall := localContactBall tau0224 center0224
def work0224 : RoundedTauEval :=
  evalTau precision tau0224 contact0224 logTwoBall

theorem center_sq0224 : (center0224.re : ℝ)^2 +
    (center0224.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0224 : work0224.theta.ok = true ∧
    work0224.jac.invOK = true ∧ acceptsUnitSq work0224.out = true := by
  norm_num [work0224, contact0224, tau0224, center0224, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0224 : CellCertificate where
  tauBall := tau0224
  contactCenter := center0224
  contactBall := contact0224
  work := work0224
  center_sq := center_sq0224
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0224.1
  jac_ok := checks0224.2.1
  accepted := checks0224.2.2

def tau0225 : RatBall :=
  ⟨⟨-23/80, 11/80⟩, 3/160⟩
def center0225 : GaussianRat :=
  ⟨-19722583/100000000, 88121387/1000000000⟩
def contact0225 : RatBall := localContactBall tau0225 center0225
def work0225 : RoundedTauEval :=
  evalTau precision tau0225 contact0225 logTwoBall

theorem center_sq0225 : (center0225.re : ℝ)^2 +
    (center0225.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0225]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0225 : work0225.theta.ok = true ∧
    work0225.jac.invOK = true ∧ acceptsUnitSq work0225.out = true := by
  norm_num [work0225, contact0225, tau0225, center0225, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0225 : CellCertificate where
  tauBall := tau0225
  contactCenter := center0225
  contactBall := contact0225
  work := work0225
  center_sq := center_sq0225
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0225.1
  jac_ok := checks0225.2.1
  accepted := checks0225.2.2

def tau0226 : RatBall :=
  ⟨⟨-21/80, 11/80⟩, 3/160⟩
def center0226 : GaussianRat :=
  ⟨-90476031/500000000, 89331987/1000000000⟩
def contact0226 : RatBall := localContactBall tau0226 center0226
def work0226 : RoundedTauEval :=
  evalTau precision tau0226 contact0226 logTwoBall

theorem center_sq0226 : (center0226.re : ℝ)^2 +
    (center0226.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0226 : work0226.theta.ok = true ∧
    work0226.jac.invOK = true ∧ acceptsUnitSq work0226.out = true := by
  norm_num [work0226, contact0226, tau0226, center0226, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0226 : CellCertificate where
  tauBall := tau0226
  contactCenter := center0226
  contactBall := contact0226
  work := work0226
  center_sq := center_sq0226
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0226.1
  jac_ok := checks0226.2.1
  accepted := checks0226.2.2

def tau0227 : RatBall :=
  ⟨⟨-19/80, 9/80⟩, 3/160⟩
def center0227 : GaussianRat :=
  ⟨-163469111/1000000000, 36947527/500000000⟩
def contact0227 : RatBall := localContactBall tau0227 center0227
def work0227 : RoundedTauEval :=
  evalTau precision tau0227 contact0227 logTwoBall

theorem center_sq0227 : (center0227.re : ℝ)^2 +
    (center0227.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0227]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0227 : work0227.theta.ok = true ∧
    work0227.jac.invOK = true ∧ acceptsUnitSq work0227.out = true := by
  norm_num [work0227, contact0227, tau0227, center0227, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0227 : CellCertificate where
  tauBall := tau0227
  contactCenter := center0227
  contactBall := contact0227
  work := work0227
  center_sq := center_sq0227
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0227.1
  jac_ok := checks0227.2.1
  accepted := checks0227.2.2

def tau0228 : RatBall :=
  ⟨⟨-17/80, 9/80⟩, 3/160⟩
def center0228 : GaussianRat :=
  ⟨-29368329/200000000, 18684497/250000000⟩
def contact0228 : RatBall := localContactBall tau0228 center0228
def work0228 : RoundedTauEval :=
  evalTau precision tau0228 contact0228 logTwoBall

theorem center_sq0228 : (center0228.re : ℝ)^2 +
    (center0228.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0228]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0228 : work0228.theta.ok = true ∧
    work0228.jac.invOK = true ∧ acceptsUnitSq work0228.out = true := by
  norm_num [work0228, contact0228, tau0228, center0228, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0228 : CellCertificate where
  tauBall := tau0228
  contactCenter := center0228
  contactBall := contact0228
  work := work0228
  center_sq := center_sq0228
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0228.1
  jac_ok := checks0228.2.1
  accepted := checks0228.2.2

def tau0229 : RatBall :=
  ⟨⟨-19/80, 11/80⟩, 3/160⟩
def center0229 : GaussianRat :=
  ⟨-82225973/500000000, 18092371/200000000⟩
def contact0229 : RatBall := localContactBall tau0229 center0229
def work0229 : RoundedTauEval :=
  evalTau precision tau0229 contact0229 logTwoBall

theorem center_sq0229 : (center0229.re : ℝ)^2 +
    (center0229.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0229]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0229 : work0229.theta.ok = true ∧
    work0229.jac.invOK = true ∧ acceptsUnitSq work0229.out = true := by
  norm_num [work0229, contact0229, tau0229, center0229, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0229 : CellCertificate where
  tauBall := tau0229
  contactCenter := center0229
  contactBall := contact0229
  work := work0229
  center_sq := center_sq0229
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0229.1
  jac_ok := checks0229.2.1
  accepted := checks0229.2.2

def tau0230 : RatBall :=
  ⟨⟨-17/80, 11/80⟩, 3/160⟩
def center0230 : GaussianRat :=
  ⟨-1154229/7812500, 91503559/1000000000⟩
def contact0230 : RatBall := localContactBall tau0230 center0230
def work0230 : RoundedTauEval :=
  evalTau precision tau0230 contact0230 logTwoBall

theorem center_sq0230 : (center0230.re : ℝ)^2 +
    (center0230.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0230]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0230 : work0230.theta.ok = true ∧
    work0230.jac.invOK = true ∧ acceptsUnitSq work0230.out = true := by
  norm_num [work0230, contact0230, tau0230, center0230, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0230 : CellCertificate where
  tauBall := tau0230
  contactCenter := center0230
  contactBall := contact0230
  work := work0230
  center_sq := center_sq0230
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0230.1
  jac_ok := checks0230.2.1
  accepted := checks0230.2.2

def tau0231 : RatBall :=
  ⟨⟨-21/80, 13/80⟩, 3/160⟩
def center0231 : GaussianRat :=
  ⟨-4555953/25000000, 105764329/1000000000⟩
def contact0231 : RatBall := localContactBall tau0231 center0231
def work0231 : RoundedTauEval :=
  evalTau precision tau0231 contact0231 logTwoBall

theorem center_sq0231 : (center0231.re : ℝ)^2 +
    (center0231.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0231]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0231 : work0231.theta.ok = true ∧
    work0231.jac.invOK = true ∧ acceptsUnitSq work0231.out = true := by
  norm_num [work0231, contact0231, tau0231, center0231, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0231 : CellCertificate where
  tauBall := tau0231
  contactCenter := center0231
  contactBall := contact0231
  work := work0231
  center_sq := center_sq0231
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0231.1
  jac_ok := checks0231.2.1
  accepted := checks0231.2.2

def cells : List CellCertificate := [cell0224, cell0225, cell0226, cell0227, cell0228, cell0229, cell0230, cell0231]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028
