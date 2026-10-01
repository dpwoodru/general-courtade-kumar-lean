import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0072 : RatBall :=
  ⟨⟨-5/16, -9/80⟩, 3/160⟩
def center0072 : GaussianRat :=
  ⟨-106033397/500000000, -70959907/1000000000⟩
def contact0072 : RatBall := localContactBall tau0072 center0072
def work0072 : RoundedTauEval :=
  evalTau precision tau0072 contact0072 logTwoBall

theorem center_sq0072 : (center0072.re : ℝ)^2 +
    (center0072.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0072]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0072 : work0072.theta.ok = true ∧
    work0072.jac.invOK = true ∧ acceptsUnitSq work0072.out = true := by
  norm_num [work0072, contact0072, tau0072, center0072, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0072 : CellCertificate where
  tauBall := tau0072
  contactCenter := center0072
  contactBall := contact0072
  work := work0072
  center_sq := center_sq0072
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0072.1
  jac_ok := checks0072.2.1
  accepted := checks0072.2.2

def tau0073 : RatBall :=
  ⟨⟨-21/80, -13/80⟩, 3/160⟩
def center0073 : GaussianRat :=
  ⟨-4555953/25000000, -105764329/1000000000⟩
def contact0073 : RatBall := localContactBall tau0073 center0073
def work0073 : RoundedTauEval :=
  evalTau precision tau0073 contact0073 logTwoBall

theorem center_sq0073 : (center0073.re : ℝ)^2 +
    (center0073.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0073]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0073 : work0073.theta.ok = true ∧
    work0073.jac.invOK = true ∧ acceptsUnitSq work0073.out = true := by
  norm_num [work0073, contact0073, tau0073, center0073, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0073 : CellCertificate where
  tauBall := tau0073
  contactCenter := center0073
  contactBall := contact0073
  work := work0073
  center_sq := center_sq0073
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0073.1
  jac_ok := checks0073.2.1
  accepted := checks0073.2.2

def tau0074 : RatBall :=
  ⟨⟨-17/80, -3/16⟩, 3/160⟩
def center0074 : GaussianRat :=
  ⟨-150128589/1000000000, -25067823/200000000⟩
def contact0074 : RatBall := localContactBall tau0074 center0074
def work0074 : RoundedTauEval :=
  evalTau precision tau0074 contact0074 logTwoBall

theorem center_sq0074 : (center0074.re : ℝ)^2 +
    (center0074.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0074]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0074 : work0074.theta.ok = true ∧
    work0074.jac.invOK = true ∧ acceptsUnitSq work0074.out = true := by
  norm_num [work0074, contact0074, tau0074, center0074, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0074 : CellCertificate where
  tauBall := tau0074
  contactCenter := center0074
  contactBall := contact0074
  work := work0074
  center_sq := center_sq0074
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0074.1
  jac_ok := checks0074.2.1
  accepted := checks0074.2.2

def tau0075 : RatBall :=
  ⟨⟨-19/80, -13/80⟩, 3/160⟩
def center0075 : GaussianRat :=
  ⟨-41411389/250000000, -107116873/1000000000⟩
def contact0075 : RatBall := localContactBall tau0075 center0075
def work0075 : RoundedTauEval :=
  evalTau precision tau0075 contact0075 logTwoBall

theorem center_sq0075 : (center0075.re : ℝ)^2 +
    (center0075.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0075]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0075 : work0075.theta.ok = true ∧
    work0075.jac.invOK = true ∧ acceptsUnitSq work0075.out = true := by
  norm_num [work0075, contact0075, tau0075, center0075, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0075 : CellCertificate where
  tauBall := tau0075
  contactCenter := center0075
  contactBall := contact0075
  work := work0075
  center_sq := center_sq0075
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0075.1
  jac_ok := checks0075.2.1
  accepted := checks0075.2.2

def tau0076 : RatBall :=
  ⟨⟨-17/80, -13/80⟩, 3/160⟩
def center0076 : GaussianRat :=
  ⟨-148834391/1000000000, -27091123/250000000⟩
def contact0076 : RatBall := localContactBall tau0076 center0076
def work0076 : RoundedTauEval :=
  evalTau precision tau0076 contact0076 logTwoBall

theorem center_sq0076 : (center0076.re : ℝ)^2 +
    (center0076.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0076]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0076 : work0076.theta.ok = true ∧
    work0076.jac.invOK = true ∧ acceptsUnitSq work0076.out = true := by
  norm_num [work0076, contact0076, tau0076, center0076, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0076 : CellCertificate where
  tauBall := tau0076
  contactCenter := center0076
  contactBall := contact0076
  work := work0076
  center_sq := center_sq0076
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0076.1
  jac_ok := checks0076.2.1
  accepted := checks0076.2.2

def tau0077 : RatBall :=
  ⟨⟨-23/80, -11/80⟩, 3/160⟩
def center0077 : GaussianRat :=
  ⟨-19722583/100000000, -88121387/1000000000⟩
def contact0077 : RatBall := localContactBall tau0077 center0077
def work0077 : RoundedTauEval :=
  evalTau precision tau0077 contact0077 logTwoBall

theorem center_sq0077 : (center0077.re : ℝ)^2 +
    (center0077.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0077]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0077 : work0077.theta.ok = true ∧
    work0077.jac.invOK = true ∧ acceptsUnitSq work0077.out = true := by
  norm_num [work0077, contact0077, tau0077, center0077, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0077 : CellCertificate where
  tauBall := tau0077
  contactCenter := center0077
  contactBall := contact0077
  work := work0077
  center_sq := center_sq0077
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0077.1
  jac_ok := checks0077.2.1
  accepted := checks0077.2.2

def tau0078 : RatBall :=
  ⟨⟨-21/80, -11/80⟩, 3/160⟩
def center0078 : GaussianRat :=
  ⟨-90476031/500000000, -89331987/1000000000⟩
def contact0078 : RatBall := localContactBall tau0078 center0078
def work0078 : RoundedTauEval :=
  evalTau precision tau0078 contact0078 logTwoBall

theorem center_sq0078 : (center0078.re : ℝ)^2 +
    (center0078.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0078]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0078 : work0078.theta.ok = true ∧
    work0078.jac.invOK = true ∧ acceptsUnitSq work0078.out = true := by
  norm_num [work0078, contact0078, tau0078, center0078, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0078 : CellCertificate where
  tauBall := tau0078
  contactCenter := center0078
  contactBall := contact0078
  work := work0078
  center_sq := center_sq0078
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0078.1
  jac_ok := checks0078.2.1
  accepted := checks0078.2.2

def tau0079 : RatBall :=
  ⟨⟨-23/80, -9/80⟩, 3/160⟩
def center0079 : GaussianRat :=
  ⟨-196096551/1000000000, -71999991/1000000000⟩
def contact0079 : RatBall := localContactBall tau0079 center0079
def work0079 : RoundedTauEval :=
  evalTau precision tau0079 contact0079 logTwoBall

theorem center_sq0079 : (center0079.re : ℝ)^2 +
    (center0079.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0079]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0079 : work0079.theta.ok = true ∧
    work0079.jac.invOK = true ∧ acceptsUnitSq work0079.out = true := by
  norm_num [work0079, contact0079, tau0079, center0079, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0079 : CellCertificate where
  tauBall := tau0079
  contactCenter := center0079
  contactBall := contact0079
  work := work0079
  center_sq := center_sq0079
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0079.1
  jac_ok := checks0079.2.1
  accepted := checks0079.2.2

def cells : List CellCertificate := [cell0072, cell0073, cell0074, cell0075, cell0076, cell0077, cell0078, cell0079]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009
