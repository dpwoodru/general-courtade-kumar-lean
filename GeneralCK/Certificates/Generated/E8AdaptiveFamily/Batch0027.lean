import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0216 : RatBall :=
  ⟨⟨-23/80, 7/80⟩, 3/160⟩
def center0216 : GaussianRat :=
  ⟨-195201217/1000000000, 13984569/250000000⟩
def contact0216 : RatBall := localContactBall tau0216 center0216
def work0216 : RoundedTauEval :=
  evalTau precision tau0216 contact0216 logTwoBall

theorem center_sq0216 : (center0216.re : ℝ)^2 +
    (center0216.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0216]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0216 : work0216.theta.ok = true ∧
    work0216.jac.invOK = true ∧ acceptsUnitSq work0216.out = true := by
  norm_num [work0216, contact0216, tau0216, center0216, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0216 : CellCertificate where
  tauBall := tau0216
  contactCenter := center0216
  contactBall := contact0216
  work := work0216
  center_sq := center_sq0216
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0216.1
  jac_ok := checks0216.2.1
  accepted := checks0216.2.2

def tau0217 : RatBall :=
  ⟨⟨-21/80, 7/80⟩, 3/160⟩
def center0217 : GaussianRat :=
  ⟨-17905297/100000000, 5669463/100000000⟩
def contact0217 : RatBall := localContactBall tau0217 center0217
def work0217 : RoundedTauEval :=
  evalTau precision tau0217 contact0217 logTwoBall

theorem center_sq0217 : (center0217.re : ℝ)^2 +
    (center0217.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0217]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0217 : work0217.theta.ok = true ∧
    work0217.jac.invOK = true ∧ acceptsUnitSq work0217.out = true := by
  norm_num [work0217, contact0217, tau0217, center0217, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0217 : CellCertificate where
  tauBall := tau0217
  contactCenter := center0217
  contactBall := contact0217
  work := work0217
  center_sq := center_sq0217
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0217.1
  jac_ok := checks0217.2.1
  accepted := checks0217.2.2

def tau0218 : RatBall :=
  ⟨⟨-19/80, 1/16⟩, 3/160⟩
def center0218 : GaussianRat :=
  ⟨-81055451/500000000, 40960501/1000000000⟩
def contact0218 : RatBall := localContactBall tau0218 center0218
def work0218 : RoundedTauEval :=
  evalTau precision tau0218 contact0218 logTwoBall

theorem center_sq0218 : (center0218.re : ℝ)^2 +
    (center0218.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0218]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0218 : work0218.theta.ok = true ∧
    work0218.jac.invOK = true ∧ acceptsUnitSq work0218.out = true := by
  norm_num [work0218, contact0218, tau0218, center0218, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0218 : CellCertificate where
  tauBall := tau0218
  contactCenter := center0218
  contactBall := contact0218
  work := work0218
  center_sq := center_sq0218
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0218.1
  jac_ok := checks0218.2.1
  accepted := checks0218.2.2

def tau0219 : RatBall :=
  ⟨⟨-17/80, 1/16⟩, 3/160⟩
def center0219 : GaussianRat :=
  ⟨-29119789/200000000, 10355411/250000000⟩
def contact0219 : RatBall := localContactBall tau0219 center0219
def work0219 : RoundedTauEval :=
  evalTau precision tau0219 contact0219 logTwoBall

theorem center_sq0219 : (center0219.re : ℝ)^2 +
    (center0219.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0219]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0219 : work0219.theta.ok = true ∧
    work0219.jac.invOK = true ∧ acceptsUnitSq work0219.out = true := by
  norm_num [work0219, contact0219, tau0219, center0219, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0219 : CellCertificate where
  tauBall := tau0219
  contactCenter := center0219
  contactBall := contact0219
  work := work0219
  center_sq := center_sq0219
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0219.1
  jac_ok := checks0219.2.1
  accepted := checks0219.2.2

def tau0220 : RatBall :=
  ⟨⟨-19/80, 7/80⟩, 3/160⟩
def center0220 : GaussianRat :=
  ⟨-162690477/1000000000, 28700003/500000000⟩
def contact0220 : RatBall := localContactBall tau0220 center0220
def work0220 : RoundedTauEval :=
  evalTau precision tau0220 contact0220 logTwoBall

theorem center_sq0220 : (center0220.re : ℝ)^2 +
    (center0220.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0220]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0220 : work0220.theta.ok = true ∧
    work0220.jac.invOK = true ∧ acceptsUnitSq work0220.out = true := by
  norm_num [work0220, contact0220, tau0220, center0220, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0220 : CellCertificate where
  tauBall := tau0220
  contactCenter := center0220
  contactBall := contact0220
  work := work0220
  center_sq := center_sq0220
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0220.1
  jac_ok := checks0220.2.1
  accepted := checks0220.2.2

def tau0221 : RatBall :=
  ⟨⟨-17/80, 7/80⟩, 3/160⟩
def center0221 : GaussianRat :=
  ⟨-146129149/1000000000, 3628117/62500000⟩
def contact0221 : RatBall := localContactBall tau0221 center0221
def work0221 : RoundedTauEval :=
  evalTau precision tau0221 contact0221 logTwoBall

theorem center_sq0221 : (center0221.re : ℝ)^2 +
    (center0221.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0221]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0221 : work0221.theta.ok = true ∧
    work0221.jac.invOK = true ∧ acceptsUnitSq work0221.out = true := by
  norm_num [work0221, contact0221, tau0221, center0221, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0221 : CellCertificate where
  tauBall := tau0221
  contactCenter := center0221
  contactBall := contact0221
  work := work0221
  center_sq := center_sq0221
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0221.1
  jac_ok := checks0221.2.1
  accepted := checks0221.2.2

def tau0222 : RatBall :=
  ⟨⟨-5/16, 9/80⟩, 3/160⟩
def center0222 : GaussianRat :=
  ⟨-106033397/500000000, 70959907/1000000000⟩
def contact0222 : RatBall := localContactBall tau0222 center0222
def work0222 : RoundedTauEval :=
  evalTau precision tau0222 contact0222 logTwoBall

theorem center_sq0222 : (center0222.re : ℝ)^2 +
    (center0222.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0222]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0222 : work0222.theta.ok = true ∧
    work0222.jac.invOK = true ∧ acceptsUnitSq work0222.out = true := by
  norm_num [work0222, contact0222, tau0222, center0222, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0222 : CellCertificate where
  tauBall := tau0222
  contactCenter := center0222
  contactBall := contact0222
  work := work0222
  center_sq := center_sq0222
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0222.1
  jac_ok := checks0222.2.1
  accepted := checks0222.2.2

def tau0223 : RatBall :=
  ⟨⟨-23/80, 9/80⟩, 3/160⟩
def center0223 : GaussianRat :=
  ⟨-196096551/1000000000, 71999991/1000000000⟩
def contact0223 : RatBall := localContactBall tau0223 center0223
def work0223 : RoundedTauEval :=
  evalTau precision tau0223 contact0223 logTwoBall

theorem center_sq0223 : (center0223.re : ℝ)^2 +
    (center0223.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0223]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0223 : work0223.theta.ok = true ∧
    work0223.jac.invOK = true ∧ acceptsUnitSq work0223.out = true := by
  norm_num [work0223, contact0223, tau0223, center0223, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0223 : CellCertificate where
  tauBall := tau0223
  contactCenter := center0223
  contactBall := contact0223
  work := work0223
  center_sq := center_sq0223
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0223.1
  jac_ok := checks0223.2.1
  accepted := checks0223.2.2

def cells : List CellCertificate := [cell0216, cell0217, cell0218, cell0219, cell0220, cell0221, cell0222, cell0223]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027
