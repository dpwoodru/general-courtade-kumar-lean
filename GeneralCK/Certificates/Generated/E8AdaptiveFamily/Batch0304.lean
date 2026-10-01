import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0304

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2432 : RatBall :=
  ⟨⟨73/320, 89/320⟩, 3/640⟩
def center2432 : GaussianRat :=
  ⟨6705983/40000000, 46671637/250000000⟩
def contact2432 : RatBall := localContactBall tau2432 center2432
def work2432 : RoundedTauEval :=
  evalTau precision tau2432 contact2432 logTwoBall

theorem center_sq2432 : (center2432.re : ℝ)^2 +
    (center2432.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2432]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2432 : work2432.theta.ok = true ∧
    work2432.jac.invOK = true ∧ acceptsUnitSq work2432.out = true := by
  norm_num [work2432, contact2432, tau2432, center2432, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2432 : CellCertificate where
  tauBall := tau2432
  contactCenter := center2432
  contactBall := contact2432
  work := work2432
  center_sq := center_sq2432
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2432.1
  jac_ok := checks2432.2.1
  accepted := checks2432.2.2

def tau2433 : RatBall :=
  ⟨⟨15/64, 89/320⟩, 3/640⟩
def center2433 : GaussianRat :=
  ⟨21501427/125000000, 186088727/1000000000⟩
def contact2433 : RatBall := localContactBall tau2433 center2433
def work2433 : RoundedTauEval :=
  evalTau precision tau2433 contact2433 logTwoBall

theorem center_sq2433 : (center2433.re : ℝ)^2 +
    (center2433.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2433]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2433 : work2433.theta.ok = true ∧
    work2433.jac.invOK = true ∧ acceptsUnitSq work2433.out = true := by
  norm_num [work2433, contact2433, tau2433, center2433, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2433 : CellCertificate where
  tauBall := tau2433
  contactCenter := center2433
  contactBall := contact2433
  work := work2433
  center_sq := center_sq2433
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2433.1
  jac_ok := checks2433.2.1
  accepted := checks2433.2.2

def tau2434 : RatBall :=
  ⟨⟨73/320, 91/320⟩, 3/640⟩
def center2434 : GaussianRat :=
  ⟨33649989/200000000, 38212623/200000000⟩
def contact2434 : RatBall := localContactBall tau2434 center2434
def work2434 : RoundedTauEval :=
  evalTau precision tau2434 contact2434 logTwoBall

theorem center_sq2434 : (center2434.re : ℝ)^2 +
    (center2434.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2434]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2434 : work2434.theta.ok = true ∧
    work2434.jac.invOK = true ∧ acceptsUnitSq work2434.out = true := by
  norm_num [work2434, contact2434, tau2434, center2434, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2434 : CellCertificate where
  tauBall := tau2434
  contactCenter := center2434
  contactBall := contact2434
  work := work2434
  center_sq := center_sq2434
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2434.1
  jac_ok := checks2434.2.1
  accepted := checks2434.2.2

def tau2435 : RatBall :=
  ⟨⟨15/64, 91/320⟩, 3/640⟩
def center2435 : GaussianRat :=
  ⟨34524793/200000000, 2380599/12500000⟩
def contact2435 : RatBall := localContactBall tau2435 center2435
def work2435 : RoundedTauEval :=
  evalTau precision tau2435 contact2435 logTwoBall

theorem center_sq2435 : (center2435.re : ℝ)^2 +
    (center2435.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2435]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2435 : work2435.theta.ok = true ∧
    work2435.jac.invOK = true ∧ acceptsUnitSq work2435.out = true := by
  norm_num [work2435, contact2435, tau2435, center2435, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2435 : CellCertificate where
  tauBall := tau2435
  contactCenter := center2435
  contactBall := contact2435
  work := work2435
  center_sq := center_sq2435
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2435.1
  jac_ok := checks2435.2.1
  accepted := checks2435.2.2

def tau2436 : RatBall :=
  ⟨⟨77/320, 89/320⟩, 3/640⟩
def center2436 : GaussianRat :=
  ⟨88177939/500000000, 185479027/1000000000⟩
def contact2436 : RatBall := localContactBall tau2436 center2436
def work2436 : RoundedTauEval :=
  evalTau precision tau2436 contact2436 logTwoBall

theorem center_sq2436 : (center2436.re : ℝ)^2 +
    (center2436.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2436]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2436 : work2436.theta.ok = true ∧
    work2436.jac.invOK = true ∧ acceptsUnitSq work2436.out = true := by
  norm_num [work2436, contact2436, tau2436, center2436, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2436 : CellCertificate where
  tauBall := tau2436
  contactCenter := center2436
  contactBall := contact2436
  work := work2436
  center_sq := center_sq2436
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2436.1
  jac_ok := checks2436.2.1
  accepted := checks2436.2.2

def tau2437 : RatBall :=
  ⟨⟨79/320, 89/320⟩, 3/640⟩
def center2437 : GaussianRat :=
  ⟨22585333/125000000, 184857737/1000000000⟩
def contact2437 : RatBall := localContactBall tau2437 center2437
def work2437 : RoundedTauEval :=
  evalTau precision tau2437 contact2437 logTwoBall

theorem center_sq2437 : (center2437.re : ℝ)^2 +
    (center2437.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2437]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2437 : work2437.theta.ok = true ∧
    work2437.jac.invOK = true ∧ acceptsUnitSq work2437.out = true := by
  norm_num [work2437, contact2437, tau2437, center2437, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2437 : CellCertificate where
  tauBall := tau2437
  contactCenter := center2437
  contactBall := contact2437
  work := work2437
  center_sq := center_sq2437
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2437.1
  jac_ok := checks2437.2.1
  accepted := checks2437.2.2

def tau2438 : RatBall :=
  ⟨⟨77/320, 91/320⟩, 3/640⟩
def center2438 : GaussianRat :=
  ⟨17698031/100000000, 94910271/500000000⟩
def contact2438 : RatBall := localContactBall tau2438 center2438
def work2438 : RoundedTauEval :=
  evalTau precision tau2438 contact2438 logTwoBall

theorem center_sq2438 : (center2438.re : ℝ)^2 +
    (center2438.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2438]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2438 : work2438.theta.ok = true ∧
    work2438.jac.invOK = true ∧ acceptsUnitSq work2438.out = true := by
  norm_num [work2438, contact2438, tau2438, center2438, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2438 : CellCertificate where
  tauBall := tau2438
  contactCenter := center2438
  contactBall := contact2438
  work := work2438
  center_sq := center_sq2438
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2438.1
  jac_ok := checks2438.2.1
  accepted := checks2438.2.2

def tau2439 : RatBall :=
  ⟨⟨79/320, 91/320⟩, 3/640⟩
def center2439 : GaussianRat :=
  ⟨181318681/1000000000, 189181283/1000000000⟩
def contact2439 : RatBall := localContactBall tau2439 center2439
def work2439 : RoundedTauEval :=
  evalTau precision tau2439 contact2439 logTwoBall

theorem center_sq2439 : (center2439.re : ℝ)^2 +
    (center2439.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2439]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2439 : work2439.theta.ok = true ∧
    work2439.jac.invOK = true ∧ acceptsUnitSq work2439.out = true := by
  norm_num [work2439, contact2439, tau2439, center2439, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2439 : CellCertificate where
  tauBall := tau2439
  contactCenter := center2439
  contactBall := contact2439
  work := work2439
  center_sq := center_sq2439
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2439.1
  jac_ok := checks2439.2.1
  accepted := checks2439.2.2

def cells : List CellCertificate := [cell2432, cell2433, cell2434, cell2435, cell2436, cell2437, cell2438, cell2439]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0304
