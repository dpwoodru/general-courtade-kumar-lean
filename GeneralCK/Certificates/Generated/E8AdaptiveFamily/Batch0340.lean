import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0340

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2720 : RatBall :=
  ⟨⟨-121/640, -221/640⟩, 3/1280⟩
def center2720 : GaussianRat :=
  ⟨-146422507/1000000000, -9563167/40000000⟩
def contact2720 : RatBall := localContactBall tau2720 center2720
def work2720 : RoundedTauEval :=
  evalTau precision tau2720 contact2720 logTwoBall

theorem center_sq2720 : (center2720.re : ℝ)^2 +
    (center2720.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2720]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2720 : work2720.theta.ok = true ∧
    work2720.jac.invOK = true ∧ acceptsUnitSq work2720.out = true := by
  norm_num [work2720, contact2720, tau2720, center2720, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2720 : CellCertificate where
  tauBall := tau2720
  contactCenter := center2720
  contactBall := contact2720
  work := work2720
  center_sq := center_sq2720
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2720.1
  jac_ok := checks2720.2.1
  accepted := checks2720.2.2

def tau2721 : RatBall :=
  ⟨⟨-63/640, -249/640⟩, 3/1280⟩
def center2721 : GaussianRat :=
  ⟨-16077783/200000000, -281560103/1000000000⟩
def contact2721 : RatBall := localContactBall tau2721 center2721
def work2721 : RoundedTauEval :=
  evalTau precision tau2721 contact2721 logTwoBall

theorem center_sq2721 : (center2721.re : ℝ)^2 +
    (center2721.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2721]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2721 : work2721.theta.ok = true ∧
    work2721.jac.invOK = true ∧ acceptsUnitSq work2721.out = true := by
  norm_num [work2721, contact2721, tau2721, center2721, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2721 : CellCertificate where
  tauBall := tau2721
  contactCenter := center2721
  contactBall := contact2721
  work := work2721
  center_sq := center_sq2721
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2721.1
  jac_ok := checks2721.2.1
  accepted := checks2721.2.2

def tau2722 : RatBall :=
  ⟨⟨-61/640, -249/640⟩, 3/1280⟩
def center2722 : GaussianRat :=
  ⟨-38934787/500000000, -281790577/1000000000⟩
def contact2722 : RatBall := localContactBall tau2722 center2722
def work2722 : RoundedTauEval :=
  evalTau precision tau2722 contact2722 logTwoBall

theorem center_sq2722 : (center2722.re : ℝ)^2 +
    (center2722.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2722]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2722 : work2722.theta.ok = true ∧
    work2722.jac.invOK = true ∧ acceptsUnitSq work2722.out = true := by
  norm_num [work2722, contact2722, tau2722, center2722, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2722 : CellCertificate where
  tauBall := tau2722
  contactCenter := center2722
  contactBall := contact2722
  work := work2722
  center_sq := center_sq2722
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2722.1
  jac_ok := checks2722.2.1
  accepted := checks2722.2.2

def tau2723 : RatBall :=
  ⟨⟨-59/640, -249/640⟩, 3/1280⟩
def center2723 : GaussianRat :=
  ⟨-75347127/1000000000, -8812939/31250000⟩
def contact2723 : RatBall := localContactBall tau2723 center2723
def work2723 : RoundedTauEval :=
  evalTau precision tau2723 contact2723 logTwoBall

theorem center_sq2723 : (center2723.re : ℝ)^2 +
    (center2723.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2723]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2723 : work2723.theta.ok = true ∧
    work2723.jac.invOK = true ∧ acceptsUnitSq work2723.out = true := by
  norm_num [work2723, contact2723, tau2723, center2723, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2723 : CellCertificate where
  tauBall := tau2723
  contactCenter := center2723
  contactBall := contact2723
  work := work2723
  center_sq := center_sq2723
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2723.1
  jac_ok := checks2723.2.1
  accepted := checks2723.2.2

def tau2724 : RatBall :=
  ⟨⟨-57/640, -249/640⟩, 3/1280⟩
def center2724 : GaussianRat :=
  ⟨-14564333/200000000, -70557619/250000000⟩
def contact2724 : RatBall := localContactBall tau2724 center2724
def work2724 : RoundedTauEval :=
  evalTau precision tau2724 contact2724 logTwoBall

theorem center_sq2724 : (center2724.re : ℝ)^2 +
    (center2724.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2724]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2724 : work2724.theta.ok = true ∧
    work2724.jac.invOK = true ∧ acceptsUnitSq work2724.out = true := by
  norm_num [work2724, contact2724, tau2724, center2724, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2724 : CellCertificate where
  tauBall := tau2724
  contactCenter := center2724
  contactBall := contact2724
  work := work2724
  center_sq := center_sq2724
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2724.1
  jac_ok := checks2724.2.1
  accepted := checks2724.2.2

def tau2725 : RatBall :=
  ⟨⟨-11/128, -251/640⟩, 3/1280⟩
def center2725 : GaussianRat :=
  ⟨-70500491/1000000000, -35621651/125000000⟩
def contact2725 : RatBall := localContactBall tau2725 center2725
def work2725 : RoundedTauEval :=
  evalTau precision tau2725 contact2725 logTwoBall

theorem center_sq2725 : (center2725.re : ℝ)^2 +
    (center2725.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2725]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2725 : work2725.theta.ok = true ∧
    work2725.jac.invOK = true ∧ acceptsUnitSq work2725.out = true := by
  norm_num [work2725, contact2725, tau2725, center2725, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2725 : CellCertificate where
  tauBall := tau2725
  contactCenter := center2725
  contactBall := contact2725
  work := work2725
  center_sq := center_sq2725
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2725.1
  jac_ok := checks2725.2.1
  accepted := checks2725.2.2

def tau2726 : RatBall :=
  ⟨⟨-53/640, -251/640⟩, 3/1280⟩
def center2726 : GaussianRat :=
  ⟨-67962093/1000000000, -285178227/1000000000⟩
def contact2726 : RatBall := localContactBall tau2726 center2726
def work2726 : RoundedTauEval :=
  evalTau precision tau2726 contact2726 logTwoBall

theorem center_sq2726 : (center2726.re : ℝ)^2 +
    (center2726.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2726]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2726 : work2726.theta.ok = true ∧
    work2726.jac.invOK = true ∧ acceptsUnitSq work2726.out = true := by
  norm_num [work2726, contact2726, tau2726, center2726, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2726 : CellCertificate where
  tauBall := tau2726
  contactCenter := center2726
  contactBall := contact2726
  work := work2726
  center_sq := center_sq2726
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2726.1
  jac_ok := checks2726.2.1
  accepted := checks2726.2.2

def tau2727 : RatBall :=
  ⟨⟨-11/128, -249/640⟩, 3/1280⟩
def center2727 : GaussianRat :=
  ⟨-70293283/1000000000, -14121991/50000000⟩
def contact2727 : RatBall := localContactBall tau2727 center2727
def work2727 : RoundedTauEval :=
  evalTau precision tau2727 contact2727 logTwoBall

theorem center_sq2727 : (center2727.re : ℝ)^2 +
    (center2727.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2727]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2727 : work2727.theta.ok = true ∧
    work2727.jac.invOK = true ∧ acceptsUnitSq work2727.out = true := by
  norm_num [work2727, contact2727, tau2727, center2727, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2727 : CellCertificate where
  tauBall := tau2727
  contactCenter := center2727
  contactBall := contact2727
  work := work2727
  center_sq := center_sq2727
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2727.1
  jac_ok := checks2727.2.1
  accepted := checks2727.2.2

def cells : List CellCertificate := [cell2720, cell2721, cell2722, cell2723, cell2724, cell2725, cell2726, cell2727]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0340
