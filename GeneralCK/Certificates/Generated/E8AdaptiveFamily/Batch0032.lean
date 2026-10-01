import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0256 : RatBall :=
  ⟨⟨-9/80, 19/80⟩, 3/160⟩
def center0256 : GaussianRat :=
  ⟨-20589547/250000000, 33110861/200000000⟩
def contact0256 : RatBall := localContactBall tau0256 center0256
def work0256 : RoundedTauEval :=
  evalTau precision tau0256 contact0256 logTwoBall

theorem center_sq0256 : (center0256.re : ℝ)^2 +
    (center0256.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0256]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0256 : work0256.theta.ok = true ∧
    work0256.jac.invOK = true ∧ acceptsUnitSq work0256.out = true := by
  norm_num [work0256, contact0256, tau0256, center0256, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0256 : CellCertificate where
  tauBall := tau0256
  contactCenter := center0256
  contactBall := contact0256
  work := work0256
  center_sq := center_sq0256
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0256.1
  jac_ok := checks0256.2.1
  accepted := checks0256.2.2

def tau0257 : RatBall :=
  ⟨⟨-7/80, 17/80⟩, 3/160⟩
def center0257 : GaussianRat :=
  ⟨-31712973/500000000, 37096923/250000000⟩
def contact0257 : RatBall := localContactBall tau0257 center0257
def work0257 : RoundedTauEval :=
  evalTau precision tau0257 contact0257 logTwoBall

theorem center_sq0257 : (center0257.re : ℝ)^2 +
    (center0257.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0257]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0257 : work0257.theta.ok = true ∧
    work0257.jac.invOK = true ∧ acceptsUnitSq work0257.out = true := by
  norm_num [work0257, contact0257, tau0257, center0257, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0257 : CellCertificate where
  tauBall := tau0257
  contactCenter := center0257
  contactBall := contact0257
  work := work0257
  center_sq := center_sq0257
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0257.1
  jac_ok := checks0257.2.1
  accepted := checks0257.2.2

def tau0258 : RatBall :=
  ⟨⟨-1/16, 17/80⟩, 3/160⟩
def center0258 : GaussianRat :=
  ⟨-22688687/500000000, 149010417/1000000000⟩
def contact0258 : RatBall := localContactBall tau0258 center0258
def work0258 : RoundedTauEval :=
  evalTau precision tau0258 contact0258 logTwoBall

theorem center_sq0258 : (center0258.re : ℝ)^2 +
    (center0258.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0258]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0258 : work0258.theta.ok = true ∧
    work0258.jac.invOK = true ∧ acceptsUnitSq work0258.out = true := by
  norm_num [work0258, contact0258, tau0258, center0258, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0258 : CellCertificate where
  tauBall := tau0258
  contactCenter := center0258
  contactBall := contact0258
  work := work0258
  center_sq := center_sq0258
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0258.1
  jac_ok := checks0258.2.1
  accepted := checks0258.2.2

def tau0259 : RatBall :=
  ⟨⟨-7/80, 19/80⟩, 3/160⟩
def center0259 : GaussianRat :=
  ⟨-32100469/500000000, 83247331/500000000⟩
def contact0259 : RatBall := localContactBall tau0259 center0259
def work0259 : RoundedTauEval :=
  evalTau precision tau0259 contact0259 logTwoBall

theorem center_sq0259 : (center0259.re : ℝ)^2 +
    (center0259.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0259]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0259 : work0259.theta.ok = true ∧
    work0259.jac.invOK = true ∧ acceptsUnitSq work0259.out = true := by
  norm_num [work0259, contact0259, tau0259, center0259, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0259 : CellCertificate where
  tauBall := tau0259
  contactCenter := center0259
  contactBall := contact0259
  work := work0259
  center_sq := center_sq0259
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0259.1
  jac_ok := checks0259.2.1
  accepted := checks0259.2.2

def tau0260 : RatBall :=
  ⟨⟨-1/16, 19/80⟩, 3/160⟩
def center0260 : GaussianRat :=
  ⟨-45935893/1000000000, 836037/5000000⟩
def contact0260 : RatBall := localContactBall tau0260 center0260
def work0260 : RoundedTauEval :=
  evalTau precision tau0260 contact0260 logTwoBall

theorem center_sq0260 : (center0260.re : ℝ)^2 +
    (center0260.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0260]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0260 : work0260.theta.ok = true ∧
    work0260.jac.invOK = true ∧ acceptsUnitSq work0260.out = true := by
  norm_num [work0260, contact0260, tau0260, center0260, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0260 : CellCertificate where
  tauBall := tau0260
  contactCenter := center0260
  contactBall := contact0260
  work := work0260
  center_sq := center_sq0260
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0260.1
  jac_ok := checks0260.2.1
  accepted := checks0260.2.2

def tau0261 : RatBall :=
  ⟨⟨-3/80, 17/80⟩, 3/160⟩
def center0261 : GaussianRat :=
  ⟨-13627917/500000000, 149428611/1000000000⟩
def contact0261 : RatBall := localContactBall tau0261 center0261
def work0261 : RoundedTauEval :=
  evalTau precision tau0261 contact0261 logTwoBall

theorem center_sq0261 : (center0261.re : ℝ)^2 +
    (center0261.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0261]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0261 : work0261.theta.ok = true ∧
    work0261.jac.invOK = true ∧ acceptsUnitSq work0261.out = true := by
  norm_num [work0261, contact0261, tau0261, center0261, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0261 : CellCertificate where
  tauBall := tau0261
  contactCenter := center0261
  contactBall := contact0261
  work := work0261
  center_sq := center_sq0261
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0261.1
  jac_ok := checks0261.2.1
  accepted := checks0261.2.2

def tau0262 : RatBall :=
  ⟨⟨-1/80, 17/80⟩, 3/160⟩
def center0262 : GaussianRat :=
  ⟨-2272549/250000000, 14963863/100000000⟩
def contact0262 : RatBall := localContactBall tau0262 center0262
def work0262 : RoundedTauEval :=
  evalTau precision tau0262 contact0262 logTwoBall

theorem center_sq0262 : (center0262.re : ℝ)^2 +
    (center0262.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0262]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0262 : work0262.theta.ok = true ∧
    work0262.jac.invOK = true ∧ acceptsUnitSq work0262.out = true := by
  norm_num [work0262, contact0262, tau0262, center0262, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0262 : CellCertificate where
  tauBall := tau0262
  contactCenter := center0262
  contactBall := contact0262
  work := work0262
  center_sq := center_sq0262
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0262.1
  jac_ok := checks0262.2.1
  accepted := checks0262.2.2

def tau0263 : RatBall :=
  ⟨⟨-3/80, 19/80⟩, 3/160⟩
def center0263 : GaussianRat :=
  ⟨-551859/20000000, 167686167/1000000000⟩
def contact0263 : RatBall := localContactBall tau0263 center0263
def work0263 : RoundedTauEval :=
  evalTau precision tau0263 contact0263 logTwoBall

theorem center_sq0263 : (center0263.re : ℝ)^2 +
    (center0263.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0263]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0263 : work0263.theta.ok = true ∧
    work0263.jac.invOK = true ∧ acceptsUnitSq work0263.out = true := by
  norm_num [work0263, contact0263, tau0263, center0263, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0263 : CellCertificate where
  tauBall := tau0263
  contactCenter := center0263
  contactBall := contact0263
  work := work0263
  center_sq := center_sq0263
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0263.1
  jac_ok := checks0263.2.1
  accepted := checks0263.2.2

def cells : List CellCertificate := [cell0256, cell0257, cell0258, cell0259, cell0260, cell0261, cell0262, cell0263]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032
