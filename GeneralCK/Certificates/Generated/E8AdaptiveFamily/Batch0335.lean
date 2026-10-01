import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0335

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2680 : RatBall :=
  ⟨⟨-17/128, -237/640⟩, 3/1280⟩
def center2680 : GaussianRat :=
  ⟨-106097509/1000000000, -131912477/500000000⟩
def contact2680 : RatBall := localContactBall tau2680 center2680
def work2680 : RoundedTauEval :=
  evalTau precision tau2680 contact2680 logTwoBall

theorem center_sq2680 : (center2680.re : ℝ)^2 +
    (center2680.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2680]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2680 : work2680.theta.ok = true ∧
    work2680.jac.invOK = true ∧ acceptsUnitSq work2680.out = true := by
  norm_num [work2680, contact2680, tau2680, center2680, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2680 : CellCertificate where
  tauBall := tau2680
  contactCenter := center2680
  contactBall := contact2680
  work := work2680
  center_sq := center_sq2680
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2680.1
  jac_ok := checks2680.2.1
  accepted := checks2680.2.2

def tau2681 : RatBall :=
  ⟨⟨-83/640, -239/640⟩, 3/1280⟩
def center2681 : GaussianRat :=
  ⟨-103935163/1000000000, -66638159/250000000⟩
def contact2681 : RatBall := localContactBall tau2681 center2681
def work2681 : RoundedTauEval :=
  evalTau precision tau2681 contact2681 logTwoBall

theorem center_sq2681 : (center2681.re : ℝ)^2 +
    (center2681.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2681]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2681 : work2681.theta.ok = true ∧
    work2681.jac.invOK = true ∧ acceptsUnitSq work2681.out = true := by
  norm_num [work2681, contact2681, tau2681, center2681, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2681 : CellCertificate where
  tauBall := tau2681
  contactCenter := center2681
  contactBall := contact2681
  work := work2681
  center_sq := center_sq2681
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2681.1
  jac_ok := checks2681.2.1
  accepted := checks2681.2.2

def tau2682 : RatBall :=
  ⟨⟨-81/640, -239/640⟩, 3/1280⟩
def center2682 : GaussianRat :=
  ⟨-50741661/500000000, -53366229/200000000⟩
def contact2682 : RatBall := localContactBall tau2682 center2682
def work2682 : RoundedTauEval :=
  evalTau precision tau2682 contact2682 logTwoBall

theorem center_sq2682 : (center2682.re : ℝ)^2 +
    (center2682.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2682]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2682 : work2682.theta.ok = true ∧
    work2682.jac.invOK = true ∧ acceptsUnitSq work2682.out = true := by
  norm_num [work2682, contact2682, tau2682, center2682, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2682 : CellCertificate where
  tauBall := tau2682
  contactCenter := center2682
  contactBall := contact2682
  work := work2682
  center_sq := center_sq2682
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2682.1
  jac_ok := checks2682.2.1
  accepted := checks2682.2.2

def tau2683 : RatBall :=
  ⟨⟨-83/640, -237/640⟩, 3/1280⟩
def center2683 : GaussianRat :=
  ⟨-6478469/62500000, -132052859/500000000⟩
def contact2683 : RatBall := localContactBall tau2683 center2683
def work2683 : RoundedTauEval :=
  evalTau precision tau2683 contact2683 logTwoBall

theorem center_sq2683 : (center2683.re : ℝ)^2 +
    (center2683.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2683]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2683 : work2683.theta.ok = true ∧
    work2683.jac.invOK = true ∧ acceptsUnitSq work2683.out = true := by
  norm_num [work2683, contact2683, tau2683, center2683, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2683 : CellCertificate where
  tauBall := tau2683
  contactCenter := center2683
  contactBall := contact2683
  work := work2683
  center_sq := center_sq2683
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2683.1
  jac_ok := checks2683.2.1
  accepted := checks2683.2.2

def tau2684 : RatBall :=
  ⟨⟨-81/640, -237/640⟩, 3/1280⟩
def center2684 : GaussianRat :=
  ⟨-101209731/1000000000, -10575219/40000000⟩
def contact2684 : RatBall := localContactBall tau2684 center2684
def work2684 : RoundedTauEval :=
  evalTau precision tau2684 contact2684 logTwoBall

theorem center_sq2684 : (center2684.re : ℝ)^2 +
    (center2684.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2684]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2684 : work2684.theta.ok = true ∧
    work2684.jac.invOK = true ∧ acceptsUnitSq work2684.out = true := by
  norm_num [work2684, contact2684, tau2684, center2684, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2684 : CellCertificate where
  tauBall := tau2684
  contactCenter := center2684
  contactBall := contact2684
  work := work2684
  center_sq := center_sq2684
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2684.1
  jac_ok := checks2684.2.1
  accepted := checks2684.2.2

def tau2685 : RatBall :=
  ⟨⟨-87/640, -47/128⟩, 3/1280⟩
def center2685 : GaussianRat :=
  ⟨-21649587/200000000, -815953/3125000⟩
def contact2685 : RatBall := localContactBall tau2685 center2685
def work2685 : RoundedTauEval :=
  evalTau precision tau2685 contact2685 logTwoBall

theorem center_sq2685 : (center2685.re : ℝ)^2 +
    (center2685.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2685]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2685 : work2685.theta.ok = true ∧
    work2685.jac.invOK = true ∧ acceptsUnitSq work2685.out = true := by
  norm_num [work2685, contact2685, tau2685, center2685, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2685 : CellCertificate where
  tauBall := tau2685
  contactCenter := center2685
  contactBall := contact2685
  work := work2685
  center_sq := center_sq2685
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2685.1
  jac_ok := checks2685.2.1
  accepted := checks2685.2.2

def tau2686 : RatBall :=
  ⟨⟨-17/128, -47/128⟩, 3/1280⟩
def center2686 : GaussianRat :=
  ⟨-13226959/125000000, -130693913/500000000⟩
def contact2686 : RatBall := localContactBall tau2686 center2686
def work2686 : RoundedTauEval :=
  evalTau precision tau2686 contact2686 logTwoBall

theorem center_sq2686 : (center2686.re : ℝ)^2 +
    (center2686.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2686]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2686 : work2686.theta.ok = true ∧
    work2686.jac.invOK = true ∧ acceptsUnitSq work2686.out = true := by
  norm_num [work2686, contact2686, tau2686, center2686, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2686 : CellCertificate where
  tauBall := tau2686
  contactCenter := center2686
  contactBall := contact2686
  work := work2686
  center_sq := center_sq2686
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2686.1
  jac_ok := checks2686.2.1
  accepted := checks2686.2.2

def tau2687 : RatBall :=
  ⟨⟨-87/640, -233/640⟩, 3/1280⟩
def center2687 : GaussianRat :=
  ⟨-10796407/100000000, -129338763/500000000⟩
def contact2687 : RatBall := localContactBall tau2687 center2687
def work2687 : RoundedTauEval :=
  evalTau precision tau2687 contact2687 logTwoBall

theorem center_sq2687 : (center2687.re : ℝ)^2 +
    (center2687.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2687]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2687 : work2687.theta.ok = true ∧
    work2687.jac.invOK = true ∧ acceptsUnitSq work2687.out = true := by
  norm_num [work2687, contact2687, tau2687, center2687, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2687 : CellCertificate where
  tauBall := tau2687
  contactCenter := center2687
  contactBall := contact2687
  work := work2687
  center_sq := center_sq2687
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2687.1
  jac_ok := checks2687.2.1
  accepted := checks2687.2.2

def cells : List CellCertificate := [cell2680, cell2681, cell2682, cell2683, cell2684, cell2685, cell2686, cell2687]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0335
