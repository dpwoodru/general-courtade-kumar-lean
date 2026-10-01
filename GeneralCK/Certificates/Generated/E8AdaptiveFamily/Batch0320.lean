import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0320

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2560 : RatBall :=
  ⟨⟨83/320, 97/320⟩, 3/640⟩
def center2560 : GaussianRat :=
  ⟨9601467/50000000, 100397757/500000000⟩
def contact2560 : RatBall := localContactBall tau2560 center2560
def work2560 : RoundedTauEval :=
  evalTau precision tau2560 contact2560 logTwoBall

theorem center_sq2560 : (center2560.re : ℝ)^2 +
    (center2560.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2560]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2560 : work2560.theta.ok = true ∧
    work2560.jac.invOK = true ∧ acceptsUnitSq work2560.out = true := by
  norm_num [work2560, contact2560, tau2560, center2560, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2560 : CellCertificate where
  tauBall := tau2560
  contactCenter := center2560
  contactBall := contact2560
  work := work2560
  center_sq := center_sq2560
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2560.1
  jac_ok := checks2560.2.1
  accepted := checks2560.2.2

def tau2561 : RatBall :=
  ⟨⟨81/320, 99/320⟩, 3/640⟩
def center2561 : GaussianRat :=
  ⟨47104143/250000000, 25733387/125000000⟩
def contact2561 : RatBall := localContactBall tau2561 center2561
def work2561 : RoundedTauEval :=
  evalTau precision tau2561 contact2561 logTwoBall

theorem center_sq2561 : (center2561.re : ℝ)^2 +
    (center2561.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2561]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2561 : work2561.theta.ok = true ∧
    work2561.jac.invOK = true ∧ acceptsUnitSq work2561.out = true := by
  norm_num [work2561, contact2561, tau2561, center2561, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2561 : CellCertificate where
  tauBall := tau2561
  contactCenter := center2561
  contactBall := contact2561
  work := work2561
  center_sq := center_sq2561
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2561.1
  jac_ok := checks2561.2.1
  accepted := checks2561.2.2

def tau2562 : RatBall :=
  ⟨⟨83/320, 99/320⟩, 3/640⟩
def center2562 : GaussianRat :=
  ⟨19276477/100000000, 205127733/1000000000⟩
def contact2562 : RatBall := localContactBall tau2562 center2562
def work2562 : RoundedTauEval :=
  evalTau precision tau2562 contact2562 logTwoBall

theorem center_sq2562 : (center2562.re : ℝ)^2 +
    (center2562.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2562]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2562 : work2562.theta.ok = true ∧
    work2562.jac.invOK = true ∧ acceptsUnitSq work2562.out = true := by
  norm_num [work2562, contact2562, tau2562, center2562, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2562 : CellCertificate where
  tauBall := tau2562
  contactCenter := center2562
  contactBall := contact2562
  work := work2562
  center_sq := center_sq2562
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2562.1
  jac_ok := checks2562.2.1
  accepted := checks2562.2.2

def tau2563 : RatBall :=
  ⟨⟨17/64, 97/320⟩, 3/640⟩
def center2563 : GaussianRat :=
  ⟨49086427/250000000, 200064207/1000000000⟩
def contact2563 : RatBall := localContactBall tau2563 center2563
def work2563 : RoundedTauEval :=
  evalTau precision tau2563 contact2563 logTwoBall

theorem center_sq2563 : (center2563.re : ℝ)^2 +
    (center2563.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2563]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2563 : work2563.theta.ok = true ∧
    work2563.jac.invOK = true ∧ acceptsUnitSq work2563.out = true := by
  norm_num [work2563, contact2563, tau2563, center2563, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2563 : CellCertificate where
  tauBall := tau2563
  contactCenter := center2563
  contactBall := contact2563
  work := work2563
  center_sq := center_sq2563
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2563.1
  jac_ok := checks2563.2.1
  accepted := checks2563.2.2

def tau2564 : RatBall :=
  ⟨⟨-149/640, -209/640⟩, 3/1280⟩
def center2564 : GaussianRat :=
  ⟨-176122773/1000000000, -220393101/1000000000⟩
def contact2564 : RatBall := localContactBall tau2564 center2564
def work2564 : RoundedTauEval :=
  evalTau precision tau2564 contact2564 logTwoBall

theorem center_sq2564 : (center2564.re : ℝ)^2 +
    (center2564.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2564]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2564 : work2564.theta.ok = true ∧
    work2564.jac.invOK = true ∧ acceptsUnitSq work2564.out = true := by
  norm_num [work2564, contact2564, tau2564, center2564, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2564 : CellCertificate where
  tauBall := tau2564
  contactCenter := center2564
  contactBall := contact2564
  work := work2564
  center_sq := center_sq2564
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2564.1
  jac_ok := checks2564.2.1
  accepted := checks2564.2.2

def tau2565 : RatBall :=
  ⟨⟨-137/640, -217/640⟩, 3/1280⟩
def center2565 : GaussianRat :=
  ⟨-41023473/250000000, -231626927/1000000000⟩
def contact2565 : RatBall := localContactBall tau2565 center2565
def work2565 : RoundedTauEval :=
  evalTau precision tau2565 contact2565 logTwoBall

theorem center_sq2565 : (center2565.re : ℝ)^2 +
    (center2565.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2565]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2565 : work2565.theta.ok = true ∧
    work2565.jac.invOK = true ∧ acceptsUnitSq work2565.out = true := by
  norm_num [work2565, contact2565, tau2565, center2565, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2565 : CellCertificate where
  tauBall := tau2565
  contactCenter := center2565
  contactBall := contact2565
  work := work2565
  center_sq := center_sq2565
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2565.1
  jac_ok := checks2565.2.1
  accepted := checks2565.2.2

def tau2566 : RatBall :=
  ⟨⟨-131/640, -221/640⟩, 3/1280⟩
def center2566 : GaussianRat :=
  ⟨-157970893/1000000000, -237302543/1000000000⟩
def contact2566 : RatBall := localContactBall tau2566 center2566
def work2566 : RoundedTauEval :=
  evalTau precision tau2566 contact2566 logTwoBall

theorem center_sq2566 : (center2566.re : ℝ)^2 +
    (center2566.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2566]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2566 : work2566.theta.ok = true ∧
    work2566.jac.invOK = true ∧ acceptsUnitSq work2566.out = true := by
  norm_num [work2566, contact2566, tau2566, center2566, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2566 : CellCertificate where
  tauBall := tau2566
  contactCenter := center2566
  contactBall := contact2566
  work := work2566
  center_sq := center_sq2566
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2566.1
  jac_ok := checks2566.2.1
  accepted := checks2566.2.2

def tau2567 : RatBall :=
  ⟨⟨-129/640, -221/640⟩, 3/1280⟩
def center2567 : GaussianRat :=
  ⟨-155670749/1000000000, -118833343/500000000⟩
def contact2567 : RatBall := localContactBall tau2567 center2567
def work2567 : RoundedTauEval :=
  evalTau precision tau2567 contact2567 logTwoBall

theorem center_sq2567 : (center2567.re : ℝ)^2 +
    (center2567.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2567]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2567 : work2567.theta.ok = true ∧
    work2567.jac.invOK = true ∧ acceptsUnitSq work2567.out = true := by
  norm_num [work2567, contact2567, tau2567, center2567, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2567 : CellCertificate where
  tauBall := tau2567
  contactCenter := center2567
  contactBall := contact2567
  work := work2567
  center_sq := center_sq2567
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2567.1
  jac_ok := checks2567.2.1
  accepted := checks2567.2.2

def cells : List CellCertificate := [cell2560, cell2561, cell2562, cell2563, cell2564, cell2565, cell2566, cell2567]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0320
