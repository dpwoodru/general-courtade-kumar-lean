import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0416 : RatBall :=
  ⟨⟨-9/160, -49/160⟩, 3/320⟩
def center0416 : GaussianRat :=
  ⟨-43120523/1000000000, -109375967/500000000⟩
def contact0416 : RatBall := localContactBall tau0416 center0416
def work0416 : RoundedTauEval :=
  evalTau precision tau0416 contact0416 logTwoBall

theorem center_sq0416 : (center0416.re : ℝ)^2 +
    (center0416.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0416]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0416 : work0416.theta.ok = true ∧
    work0416.jac.invOK = true ∧ acceptsUnitSq work0416.out = true := by
  norm_num [work0416, contact0416, tau0416, center0416, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0416 : CellCertificate where
  tauBall := tau0416
  contactCenter := center0416
  contactBall := contact0416
  work := work0416
  center_sq := center_sq0416
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0416.1
  jac_ok := checks0416.2.1
  accepted := checks0416.2.2

def tau0417 : RatBall :=
  ⟨⟨-7/160, -11/32⟩, 3/320⟩
def center0417 : GaussianRat :=
  ⟨-6904519/200000000, -248189889/1000000000⟩
def contact0417 : RatBall := localContactBall tau0417 center0417
def work0417 : RoundedTauEval :=
  evalTau precision tau0417 contact0417 logTwoBall

theorem center_sq0417 : (center0417.re : ℝ)^2 +
    (center0417.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0417]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0417 : work0417.theta.ok = true ∧
    work0417.jac.invOK = true ∧ acceptsUnitSq work0417.out = true := by
  norm_num [work0417, contact0417, tau0417, center0417, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0417 : CellCertificate where
  tauBall := tau0417
  contactCenter := center0417
  contactBall := contact0417
  work := work0417
  center_sq := center_sq0417
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0417.1
  jac_ok := checks0417.2.1
  accepted := checks0417.2.2

def tau0418 : RatBall :=
  ⟨⟨-1/32, -11/32⟩, 3/320⟩
def center0418 : GaussianRat :=
  ⟨-24673061/1000000000, -248489097/1000000000⟩
def contact0418 : RatBall := localContactBall tau0418 center0418
def work0418 : RoundedTauEval :=
  evalTau precision tau0418 contact0418 logTwoBall

theorem center_sq0418 : (center0418.re : ℝ)^2 +
    (center0418.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0418]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0418 : work0418.theta.ok = true ∧
    work0418.jac.invOK = true ∧ acceptsUnitSq work0418.out = true := by
  norm_num [work0418, contact0418, tau0418, center0418, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0418 : CellCertificate where
  tauBall := tau0418
  contactCenter := center0418
  contactBall := contact0418
  work := work0418
  center_sq := center_sq0418
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0418.1
  jac_ok := checks0418.2.1
  accepted := checks0418.2.2

def tau0419 : RatBall :=
  ⟨⟨-7/160, -53/160⟩, 3/320⟩
def center0419 : GaussianRat :=
  ⟨-17091823/500000000, -119198781/500000000⟩
def contact0419 : RatBall := localContactBall tau0419 center0419
def work0419 : RoundedTauEval :=
  evalTau precision tau0419 contact0419 logTwoBall

theorem center_sq0419 : (center0419.re : ℝ)^2 +
    (center0419.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0419]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0419 : work0419.theta.ok = true ∧
    work0419.jac.invOK = true ∧ acceptsUnitSq work0419.out = true := by
  norm_num [work0419, contact0419, tau0419, center0419, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0419 : CellCertificate where
  tauBall := tau0419
  contactCenter := center0419
  contactBall := contact0419
  work := work0419
  center_sq := center_sq0419
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0419.1
  jac_ok := checks0419.2.1
  accepted := checks0419.2.2

def tau0420 : RatBall :=
  ⟨⟨-1/32, -53/160⟩, 3/320⟩
def center0420 : GaussianRat :=
  ⟨-2443029/100000000, -119340169/500000000⟩
def contact0420 : RatBall := localContactBall tau0420 center0420
def work0420 : RoundedTauEval :=
  evalTau precision tau0420 contact0420 logTwoBall

theorem center_sq0420 : (center0420.re : ℝ)^2 +
    (center0420.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0420]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0420 : work0420.theta.ok = true ∧
    work0420.jac.invOK = true ∧ acceptsUnitSq work0420.out = true := by
  norm_num [work0420, contact0420, tau0420, center0420, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0420 : CellCertificate where
  tauBall := tau0420
  contactCenter := center0420
  contactBall := contact0420
  work := work0420
  center_sq := center_sq0420
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0420.1
  jac_ok := checks0420.2.1
  accepted := checks0420.2.2

def tau0421 : RatBall :=
  ⟨⟨-3/160, -11/32⟩, 3/320⟩
def center0421 : GaussianRat :=
  ⟨-7404737/500000000, -31086129/125000000⟩
def contact0421 : RatBall := localContactBall tau0421 center0421
def work0421 : RoundedTauEval :=
  evalTau precision tau0421 contact0421 logTwoBall

theorem center_sq0421 : (center0421.re : ℝ)^2 +
    (center0421.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0421]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0421 : work0421.theta.ok = true ∧
    work0421.jac.invOK = true ∧ acceptsUnitSq work0421.out = true := by
  norm_num [work0421, contact0421, tau0421, center0421, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0421 : CellCertificate where
  tauBall := tau0421
  contactCenter := center0421
  contactBall := contact0421
  work := work0421
  center_sq := center_sq0421
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0421.1
  jac_ok := checks0421.2.1
  accepted := checks0421.2.2

def tau0422 : RatBall :=
  ⟨⟨-1/160, -11/32⟩, 3/320⟩
def center0422 : GaussianRat :=
  ⟨-617179/125000000, -248789139/1000000000⟩
def contact0422 : RatBall := localContactBall tau0422 center0422
def work0422 : RoundedTauEval :=
  evalTau precision tau0422 contact0422 logTwoBall

theorem center_sq0422 : (center0422.re : ℝ)^2 +
    (center0422.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0422]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0422 : work0422.theta.ok = true ∧
    work0422.jac.invOK = true ∧ acceptsUnitSq work0422.out = true := by
  norm_num [work0422, contact0422, tau0422, center0422, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0422 : CellCertificate where
  tauBall := tau0422
  contactCenter := center0422
  contactBall := contact0422
  work := work0422
  center_sq := center_sq0422
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0422.1
  jac_ok := checks0422.2.1
  accepted := checks0422.2.2

def tau0423 : RatBall :=
  ⟨⟨-3/160, -53/160⟩, 3/320⟩
def center0423 : GaussianRat :=
  ⟨-1832943/125000000, -238869281/1000000000⟩
def contact0423 : RatBall := localContactBall tau0423 center0423
def work0423 : RoundedTauEval :=
  evalTau precision tau0423 contact0423 logTwoBall

theorem center_sq0423 : (center0423.re : ℝ)^2 +
    (center0423.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0423]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0423 : work0423.theta.ok = true ∧
    work0423.jac.invOK = true ∧ acceptsUnitSq work0423.out = true := by
  norm_num [work0423, contact0423, tau0423, center0423, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0423 : CellCertificate where
  tauBall := tau0423
  contactCenter := center0423
  contactBall := contact0423
  work := work0423
  center_sq := center_sq0423
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0423.1
  jac_ok := checks0423.2.1
  accepted := checks0423.2.2

def cells : List CellCertificate := [cell0416, cell0417, cell0418, cell0419, cell0420, cell0421, cell0422, cell0423]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052
