import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2656 : RatBall :=
  ⟨⟨-69/640, -241/640⟩, 3/1280⟩
def center2656 : GaussianRat :=
  ⟨-10867009/125000000, -67712443/250000000⟩
def contact2656 : RatBall := localContactBall tau2656 center2656
def work2656 : RoundedTauEval :=
  evalTau precision tau2656 contact2656 logTwoBall

theorem center_sq2656 : (center2656.re : ℝ)^2 +
    (center2656.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2656]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2656 : work2656.theta.ok = true ∧
    work2656.jac.invOK = true ∧ acceptsUnitSq work2656.out = true := by
  norm_num [work2656, contact2656, tau2656, center2656, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2656 : CellCertificate where
  tauBall := tau2656
  contactCenter := center2656
  contactBall := contact2656
  work := work2656
  center_sq := center_sq2656
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2656.1
  jac_ok := checks2656.2.1
  accepted := checks2656.2.2

def tau2657 : RatBall :=
  ⟨⟨-67/640, -243/640⟩, 3/1280⟩
def center2657 : GaussianRat :=
  ⟨-42344767/500000000, -273575317/1000000000⟩
def contact2657 : RatBall := localContactBall tau2657 center2657
def work2657 : RoundedTauEval :=
  evalTau precision tau2657 contact2657 logTwoBall

theorem center_sq2657 : (center2657.re : ℝ)^2 +
    (center2657.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2657]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2657 : work2657.theta.ok = true ∧
    work2657.jac.invOK = true ∧ acceptsUnitSq work2657.out = true := by
  norm_num [work2657, contact2657, tau2657, center2657, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2657 : CellCertificate where
  tauBall := tau2657
  contactCenter := center2657
  contactBall := contact2657
  work := work2657
  center_sq := center_sq2657
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2657.1
  jac_ok := checks2657.2.1
  accepted := checks2657.2.2

def tau2658 : RatBall :=
  ⟨⟨-13/128, -243/640⟩, 3/1280⟩
def center2658 : GaussianRat :=
  ⟨-82196967/1000000000, -136904929/500000000⟩
def contact2658 : RatBall := localContactBall tau2658 center2658
def work2658 : RoundedTauEval :=
  evalTau precision tau2658 contact2658 logTwoBall

theorem center_sq2658 : (center2658.re : ℝ)^2 +
    (center2658.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2658]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2658 : work2658.theta.ok = true ∧
    work2658.jac.invOK = true ∧ acceptsUnitSq work2658.out = true := by
  norm_num [work2658, contact2658, tau2658, center2658, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2658 : CellCertificate where
  tauBall := tau2658
  contactCenter := center2658
  contactBall := contact2658
  work := work2658
  center_sq := center_sq2658
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2658.1
  jac_ok := checks2658.2.1
  accepted := checks2658.2.2

def tau2659 : RatBall :=
  ⟨⟨-67/640, -241/640⟩, 3/1280⟩
def center2659 : GaussianRat :=
  ⟨-84453299/1000000000, -5421753/20000000⟩
def contact2659 : RatBall := localContactBall tau2659 center2659
def work2659 : RoundedTauEval :=
  evalTau precision tau2659 contact2659 logTwoBall

theorem center_sq2659 : (center2659.re : ℝ)^2 +
    (center2659.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2659]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2659 : work2659.theta.ok = true ∧
    work2659.jac.invOK = true ∧ acceptsUnitSq work2659.out = true := by
  norm_num [work2659, contact2659, tau2659, center2659, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2659 : CellCertificate where
  tauBall := tau2659
  contactCenter := center2659
  contactBall := contact2659
  work := work2659
  center_sq := center_sq2659
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2659.1
  jac_ok := checks2659.2.1
  accepted := checks2659.2.2

def tau2660 : RatBall :=
  ⟨⟨-13/128, -241/640⟩, 3/1280⟩
def center2660 : GaussianRat :=
  ⟨-40983659/500000000, -135659503/500000000⟩
def contact2660 : RatBall := localContactBall tau2660 center2660
def work2660 : RoundedTauEval :=
  evalTau precision tau2660 contact2660 logTwoBall

theorem center_sq2660 : (center2660.re : ℝ)^2 +
    (center2660.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2660]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2660 : work2660.theta.ok = true ∧
    work2660.jac.invOK = true ∧ acceptsUnitSq work2660.out = true := by
  norm_num [work2660, contact2660, tau2660, center2660, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2660 : CellCertificate where
  tauBall := tau2660
  contactCenter := center2660
  contactBall := contact2660
  work := work2660
  center_sq := center_sq2660
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2660.1
  jac_ok := checks2660.2.1
  accepted := checks2660.2.2

def tau2661 : RatBall :=
  ⟨⟨-19/128, -239/640⟩, 3/1280⟩
def center2661 : GaussianRat :=
  ⟨-118563451/1000000000, -66188883/250000000⟩
def contact2661 : RatBall := localContactBall tau2661 center2661
def work2661 : RoundedTauEval :=
  evalTau precision tau2661 contact2661 logTwoBall

theorem center_sq2661 : (center2661.re : ℝ)^2 +
    (center2661.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2661]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2661 : work2661.theta.ok = true ∧
    work2661.jac.invOK = true ∧ acceptsUnitSq work2661.out = true := by
  norm_num [work2661, contact2661, tau2661, center2661, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2661 : CellCertificate where
  tauBall := tau2661
  contactCenter := center2661
  contactBall := contact2661
  work := work2661
  center_sq := center_sq2661
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2661.1
  jac_ok := checks2661.2.1
  accepted := checks2661.2.2

def tau2662 : RatBall :=
  ⟨⟨-93/640, -239/640⟩, 3/1280⟩
def center2662 : GaussianRat :=
  ⟨-116135629/1000000000, -265069807/1000000000⟩
def contact2662 : RatBall := localContactBall tau2662 center2662
def work2662 : RoundedTauEval :=
  evalTau precision tau2662 contact2662 logTwoBall

theorem center_sq2662 : (center2662.re : ℝ)^2 +
    (center2662.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2662]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2662 : work2662.theta.ok = true ∧
    work2662.jac.invOK = true ∧ acceptsUnitSq work2662.out = true := by
  norm_num [work2662, contact2662, tau2662, center2662, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2662 : CellCertificate where
  tauBall := tau2662
  contactCenter := center2662
  contactBall := contact2662
  work := work2662
  center_sq := center_sq2662
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2662.1
  jac_ok := checks2662.2.1
  accepted := checks2662.2.2

def tau2663 : RatBall :=
  ⟨⟨-19/128, -237/640⟩, 3/1280⟩
def center2663 : GaussianRat :=
  ⟨-29562099/250000000, -262332709/1000000000⟩
def contact2663 : RatBall := localContactBall tau2663 center2663
def work2663 : RoundedTauEval :=
  evalTau precision tau2663 contact2663 logTwoBall

theorem center_sq2663 : (center2663.re : ℝ)^2 +
    (center2663.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2663]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2663 : work2663.theta.ok = true ∧
    work2663.jac.invOK = true ∧ acceptsUnitSq work2663.out = true := by
  norm_num [work2663, contact2663, tau2663, center2663, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2663 : CellCertificate where
  tauBall := tau2663
  contactCenter := center2663
  contactBall := contact2663
  work := work2663
  center_sq := center_sq2663
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2663.1
  jac_ok := checks2663.2.1
  accepted := checks2663.2.2

def cells : List CellCertificate := [cell2656, cell2657, cell2658, cell2659, cell2660, cell2661, cell2662, cell2663]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332
