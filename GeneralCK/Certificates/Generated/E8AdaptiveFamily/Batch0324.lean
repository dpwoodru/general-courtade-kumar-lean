import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0324

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2592 : RatBall :=
  ⟨⟨-23/128, -45/128⟩, 3/1280⟩
def center2592 : GaussianRat :=
  ⟨-5604287/40000000, -122385171/500000000⟩
def contact2592 : RatBall := localContactBall tau2592 center2592
def work2592 : RoundedTauEval :=
  evalTau precision tau2592 contact2592 logTwoBall

theorem center_sq2592 : (center2592.re : ℝ)^2 +
    (center2592.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2592]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2592 : work2592.theta.ok = true ∧
    work2592.jac.invOK = true ∧ acceptsUnitSq work2592.out = true := by
  norm_num [work2592, contact2592, tau2592, center2592, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2592 : CellCertificate where
  tauBall := tau2592
  contactCenter := center2592
  contactBall := contact2592
  work := work2592
  center_sq := center_sq2592
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2592.1
  jac_ok := checks2592.2.1
  accepted := checks2592.2.2

def tau2593 : RatBall :=
  ⟨⟨-113/640, -45/128⟩, 3/1280⟩
def center2593 : GaussianRat :=
  ⟨-137760383/1000000000, -245107147/1000000000⟩
def contact2593 : RatBall := localContactBall tau2593 center2593
def work2593 : RoundedTauEval :=
  evalTau precision tau2593 contact2593 logTwoBall

theorem center_sq2593 : (center2593.re : ℝ)^2 +
    (center2593.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2593]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2593 : work2593.theta.ok = true ∧
    work2593.jac.invOK = true ∧ acceptsUnitSq work2593.out = true := by
  norm_num [work2593, contact2593, tau2593, center2593, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2593 : CellCertificate where
  tauBall := tau2593
  contactCenter := center2593
  contactBall := contact2593
  work := work2593
  center_sq := center_sq2593
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2593.1
  jac_ok := checks2593.2.1
  accepted := checks2593.2.2

def tau2594 : RatBall :=
  ⟨⟨-109/640, -233/640⟩, 3/1280⟩
def center2594 : GaussianRat :=
  ⟨-134387007/1000000000, -127619041/500000000⟩
def contact2594 : RatBall := localContactBall tau2594 center2594
def work2594 : RoundedTauEval :=
  evalTau precision tau2594 contact2594 logTwoBall

theorem center_sq2594 : (center2594.re : ℝ)^2 +
    (center2594.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2594]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2594 : work2594.theta.ok = true ∧
    work2594.jac.invOK = true ∧ acceptsUnitSq work2594.out = true := by
  norm_num [work2594, contact2594, tau2594, center2594, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2594 : CellCertificate where
  tauBall := tau2594
  contactCenter := center2594
  contactBall := contact2594
  work := work2594
  center_sq := center_sq2594
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2594.1
  jac_ok := checks2594.2.1
  accepted := checks2594.2.2

def tau2595 : RatBall :=
  ⟨⟨-107/640, -233/640⟩, 3/1280⟩
def center2595 : GaussianRat :=
  ⟨-132006469/1000000000, -255577867/1000000000⟩
def contact2595 : RatBall := localContactBall tau2595 center2595
def work2595 : RoundedTauEval :=
  evalTau precision tau2595 contact2595 logTwoBall

theorem center_sq2595 : (center2595.re : ℝ)^2 +
    (center2595.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2595]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2595 : work2595.theta.ok = true ∧
    work2595.jac.invOK = true ∧ acceptsUnitSq work2595.out = true := by
  norm_num [work2595, contact2595, tau2595, center2595, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2595 : CellCertificate where
  tauBall := tau2595
  contactCenter := center2595
  contactBall := contact2595
  work := work2595
  center_sq := center_sq2595
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2595.1
  jac_ok := checks2595.2.1
  accepted := checks2595.2.2

def tau2596 : RatBall :=
  ⟨⟨-21/128, -233/640⟩, 3/1280⟩
def center2596 : GaussianRat :=
  ⟨-8101339/62500000, -3998631/15625000⟩
def contact2596 : RatBall := localContactBall tau2596 center2596
def work2596 : RoundedTauEval :=
  evalTau precision tau2596 contact2596 logTwoBall

theorem center_sq2596 : (center2596.re : ℝ)^2 +
    (center2596.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2596]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2596 : work2596.theta.ok = true ∧
    work2596.jac.invOK = true ∧ acceptsUnitSq work2596.out = true := by
  norm_num [work2596, contact2596, tau2596, center2596, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2596 : CellCertificate where
  tauBall := tau2596
  contactCenter := center2596
  contactBall := contact2596
  work := work2596
  center_sq := center_sq2596
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2596.1
  jac_ok := checks2596.2.1
  accepted := checks2596.2.2

def tau2597 : RatBall :=
  ⟨⟨-99/640, -237/640⟩, 3/1280⟩
def center2597 : GaussianRat :=
  ⟨-123079793/1000000000, -65423867/250000000⟩
def contact2597 : RatBall := localContactBall tau2597 center2597
def work2597 : RoundedTauEval :=
  evalTau precision tau2597 contact2597 logTwoBall

theorem center_sq2597 : (center2597.re : ℝ)^2 +
    (center2597.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2597]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2597 : work2597.theta.ok = true ∧
    work2597.jac.invOK = true ∧ acceptsUnitSq work2597.out = true := by
  norm_num [work2597, contact2597, tau2597, center2597, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2597 : CellCertificate where
  tauBall := tau2597
  contactCenter := center2597
  contactBall := contact2597
  work := work2597
  center_sq := center_sq2597
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2597.1
  jac_ok := checks2597.2.1
  accepted := checks2597.2.2

def tau2598 : RatBall :=
  ⟨⟨-97/640, -237/640⟩, 3/1280⟩
def center2598 : GaussianRat :=
  ⟨-60333117/500000000, -6550423/25000000⟩
def contact2598 : RatBall := localContactBall tau2598 center2598
def work2598 : RoundedTauEval :=
  evalTau precision tau2598 contact2598 logTwoBall

theorem center_sq2598 : (center2598.re : ℝ)^2 +
    (center2598.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2598]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2598 : work2598.theta.ok = true ∧
    work2598.jac.invOK = true ∧ acceptsUnitSq work2598.out = true := by
  norm_num [work2598, contact2598, tau2598, center2598, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2598 : CellCertificate where
  tauBall := tau2598
  contactCenter := center2598
  contactBall := contact2598
  work := work2598
  center_sq := center_sq2598
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2598.1
  jac_ok := checks2598.2.1
  accepted := checks2598.2.2

def tau2599 : RatBall :=
  ⟨⟨-103/640, -47/128⟩, 3/1280⟩
def center2599 : GaussianRat :=
  ⟨-31890163/250000000, -51727193/200000000⟩
def contact2599 : RatBall := localContactBall tau2599 center2599
def work2599 : RoundedTauEval :=
  evalTau precision tau2599 contact2599 logTwoBall

theorem center_sq2599 : (center2599.re : ℝ)^2 +
    (center2599.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2599]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2599 : work2599.theta.ok = true ∧
    work2599.jac.invOK = true ∧ acceptsUnitSq work2599.out = true := by
  norm_num [work2599, contact2599, tau2599, center2599, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2599 : CellCertificate where
  tauBall := tau2599
  contactCenter := center2599
  contactBall := contact2599
  work := work2599
  center_sq := center_sq2599
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2599.1
  jac_ok := checks2599.2.1
  accepted := checks2599.2.2

def cells : List CellCertificate := [cell2592, cell2593, cell2594, cell2595, cell2596, cell2597, cell2598, cell2599]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0324
