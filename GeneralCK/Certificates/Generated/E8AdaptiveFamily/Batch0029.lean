import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0232 : RatBall :=
  ⟨⟨-19/80, 13/80⟩, 3/160⟩
def center0232 : GaussianRat :=
  ⟨-41411389/250000000, 107116873/1000000000⟩
def contact0232 : RatBall := localContactBall tau0232 center0232
def work0232 : RoundedTauEval :=
  evalTau precision tau0232 contact0232 logTwoBall

theorem center_sq0232 : (center0232.re : ℝ)^2 +
    (center0232.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0232]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0232 : work0232.theta.ok = true ∧
    work0232.jac.invOK = true ∧ acceptsUnitSq work0232.out = true := by
  norm_num [work0232, contact0232, tau0232, center0232, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0232 : CellCertificate where
  tauBall := tau0232
  contactCenter := center0232
  contactBall := contact0232
  work := work0232
  center_sq := center_sq0232
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0232.1
  jac_ok := checks0232.2.1
  accepted := checks0232.2.2

def tau0233 : RatBall :=
  ⟨⟨-17/80, 13/80⟩, 3/160⟩
def center0233 : GaussianRat :=
  ⟨-148834391/1000000000, 27091123/250000000⟩
def contact0233 : RatBall := localContactBall tau0233 center0233
def work0233 : RoundedTauEval :=
  evalTau precision tau0233 contact0233 logTwoBall

theorem center_sq0233 : (center0233.re : ℝ)^2 +
    (center0233.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0233]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0233 : work0233.theta.ok = true ∧
    work0233.jac.invOK = true ∧ acceptsUnitSq work0233.out = true := by
  norm_num [work0233, contact0233, tau0233, center0233, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0233 : CellCertificate where
  tauBall := tau0233
  contactCenter := center0233
  contactBall := contact0233
  work := work0233
  center_sq := center_sq0233
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0233.1
  jac_ok := checks0233.2.1
  accepted := checks0233.2.2

def tau0234 : RatBall :=
  ⟨⟨-17/80, 3/16⟩, 3/160⟩
def center0234 : GaussianRat :=
  ⟨-150128589/1000000000, 25067823/200000000⟩
def contact0234 : RatBall := localContactBall tau0234 center0234
def work0234 : RoundedTauEval :=
  evalTau precision tau0234 contact0234 logTwoBall

theorem center_sq0234 : (center0234.re : ℝ)^2 +
    (center0234.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0234]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0234 : work0234.theta.ok = true ∧
    work0234.jac.invOK = true ∧ acceptsUnitSq work0234.out = true := by
  norm_num [work0234, contact0234, tau0234, center0234, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0234 : CellCertificate where
  tauBall := tau0234
  contactCenter := center0234
  contactBall := contact0234
  work := work0234
  center_sq := center_sq0234
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0234.1
  jac_ok := checks0234.2.1
  accepted := checks0234.2.2

def tau0235 : RatBall :=
  ⟨⟨-3/16, 9/80⟩, 3/160⟩
def center0235 : GaussianRat :=
  ⟨-26005447/200000000, 37751763/500000000⟩
def contact0235 : RatBall := localContactBall tau0235 center0235
def work0235 : RoundedTauEval :=
  evalTau precision tau0235 contact0235 logTwoBall

theorem center_sq0235 : (center0235.re : ℝ)^2 +
    (center0235.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0235]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0235 : work0235.theta.ok = true ∧
    work0235.jac.invOK = true ∧ acceptsUnitSq work0235.out = true := by
  norm_num [work0235, contact0235, tau0235, center0235, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0235 : CellCertificate where
  tauBall := tau0235
  contactCenter := center0235
  contactBall := contact0235
  work := work0235
  center_sq := center_sq0235
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0235.1
  jac_ok := checks0235.2.1
  accepted := checks0235.2.2

def tau0236 : RatBall :=
  ⟨⟨-13/80, 9/80⟩, 3/160⟩
def center0236 : GaussianRat :=
  ⟨-56522129/500000000, 76186323/1000000000⟩
def contact0236 : RatBall := localContactBall tau0236 center0236
def work0236 : RoundedTauEval :=
  evalTau precision tau0236 contact0236 logTwoBall

theorem center_sq0236 : (center0236.re : ℝ)^2 +
    (center0236.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0236]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0236 : work0236.theta.ok = true ∧
    work0236.jac.invOK = true ∧ acceptsUnitSq work0236.out = true := by
  norm_num [work0236, contact0236, tau0236, center0236, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0236 : CellCertificate where
  tauBall := tau0236
  contactCenter := center0236
  contactBall := contact0236
  work := work0236
  center_sq := center_sq0236
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0236.1
  jac_ok := checks0236.2.1
  accepted := checks0236.2.2

def tau0237 : RatBall :=
  ⟨⟨-3/16, 11/80⟩, 3/160⟩
def center0237 : GaussianRat :=
  ⟨-130837509/1000000000, 92449971/1000000000⟩
def contact0237 : RatBall := localContactBall tau0237 center0237
def work0237 : RoundedTauEval :=
  evalTau precision tau0237 contact0237 logTwoBall

theorem center_sq0237 : (center0237.re : ℝ)^2 +
    (center0237.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0237]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0237 : work0237.theta.ok = true ∧
    work0237.jac.invOK = true ∧ acceptsUnitSq work0237.out = true := by
  norm_num [work0237, contact0237, tau0237, center0237, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0237 : CellCertificate where
  tauBall := tau0237
  contactCenter := center0237
  contactBall := contact0237
  work := work0237
  center_sq := center_sq0237
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0237.1
  jac_ok := checks0237.2.1
  accepted := checks0237.2.2

def tau0238 : RatBall :=
  ⟨⟨-13/80, 11/80⟩, 3/160⟩
def center0238 : GaussianRat :=
  ⟨-22751869/200000000, 46647191/500000000⟩
def contact0238 : RatBall := localContactBall tau0238 center0238
def work0238 : RoundedTauEval :=
  evalTau precision tau0238 contact0238 logTwoBall

theorem center_sq0238 : (center0238.re : ℝ)^2 +
    (center0238.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0238]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0238 : work0238.theta.ok = true ∧
    work0238.jac.invOK = true ∧ acceptsUnitSq work0238.out = true := by
  norm_num [work0238, contact0238, tau0238, center0238, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0238 : CellCertificate where
  tauBall := tau0238
  contactCenter := center0238
  contactBall := contact0238
  work := work0238
  center_sq := center_sq0238
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0238.1
  jac_ok := checks0238.2.1
  accepted := checks0238.2.2

def tau0239 : RatBall :=
  ⟨⟨-3/16, 13/80⟩, 3/160⟩
def center0239 : GaussianRat :=
  ⟨-131822371/1000000000, 13687313/125000000⟩
def contact0239 : RatBall := localContactBall tau0239 center0239
def work0239 : RoundedTauEval :=
  evalTau precision tau0239 contact0239 logTwoBall

theorem center_sq0239 : (center0239.re : ℝ)^2 +
    (center0239.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0239]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0239 : work0239.theta.ok = true ∧
    work0239.jac.invOK = true ∧ acceptsUnitSq work0239.out = true := by
  norm_num [work0239, contact0239, tau0239, center0239, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0239 : CellCertificate where
  tauBall := tau0239
  contactCenter := center0239
  contactBall := contact0239
  work := work0239
  center_sq := center_sq0239
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0239.1
  jac_ok := checks0239.2.1
  accepted := checks0239.2.2

def cells : List CellCertificate := [cell0232, cell0233, cell0234, cell0235, cell0236, cell0237, cell0238, cell0239]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029
