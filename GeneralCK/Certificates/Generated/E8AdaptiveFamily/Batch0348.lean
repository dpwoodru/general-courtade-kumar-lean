import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2784 : RatBall :=
  ⟨⟨-7/128, -251/640⟩, 3/1280⟩
def center2784 : GaussianRat :=
  ⟨-45003787/1000000000, -57338531/200000000⟩
def contact2784 : RatBall := localContactBall tau2784 center2784
def work2784 : RoundedTauEval :=
  evalTau precision tau2784 contact2784 logTwoBall

theorem center_sq2784 : (center2784.re : ℝ)^2 +
    (center2784.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2784]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2784 : work2784.theta.ok = true ∧
    work2784.jac.invOK = true ∧ acceptsUnitSq work2784.out = true := by
  norm_num [work2784, contact2784, tau2784, center2784, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2784 : CellCertificate where
  tauBall := tau2784
  contactCenter := center2784
  contactBall := contact2784
  work := work2784
  center_sq := center_sq2784
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2784.1
  jac_ok := checks2784.2.1
  accepted := checks2784.2.2

def tau2785 : RatBall :=
  ⟨⟨-33/640, -251/640⟩, 3/1280⟩
def center2785 : GaussianRat :=
  ⟨-42442179/1000000000, -286823589/1000000000⟩
def contact2785 : RatBall := localContactBall tau2785 center2785
def work2785 : RoundedTauEval :=
  evalTau precision tau2785 contact2785 logTwoBall

theorem center_sq2785 : (center2785.re : ℝ)^2 +
    (center2785.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2785]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2785 : work2785.theta.ok = true ∧
    work2785.jac.invOK = true ∧ acceptsUnitSq work2785.out = true := by
  norm_num [work2785, contact2785, tau2785, center2785, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2785 : CellCertificate where
  tauBall := tau2785
  contactCenter := center2785
  contactBall := contact2785
  work := work2785
  center_sq := center_sq2785
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2785.1
  jac_ok := checks2785.2.1
  accepted := checks2785.2.2

def tau2786 : RatBall :=
  ⟨⟨-7/128, -249/640⟩, 3/1280⟩
def center2786 : GaussianRat :=
  ⟨-22435003/500000000, -284135717/1000000000⟩
def contact2786 : RatBall := localContactBall tau2786 center2786
def work2786 : RoundedTauEval :=
  evalTau precision tau2786 contact2786 logTwoBall

theorem center_sq2786 : (center2786.re : ℝ)^2 +
    (center2786.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2786]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2786 : work2786.theta.ok = true ∧
    work2786.jac.invOK = true ∧ acceptsUnitSq work2786.out = true := by
  norm_num [work2786, contact2786, tau2786, center2786, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2786 : CellCertificate where
  tauBall := tau2786
  contactCenter := center2786
  contactBall := contact2786
  work := work2786
  center_sq := center_sq2786
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2786.1
  jac_ok := checks2786.2.1
  accepted := checks2786.2.2

def tau2787 : RatBall :=
  ⟨⟨-33/640, -249/640⟩, 3/1280⟩
def center2787 : GaussianRat :=
  ⟨-42315903/1000000000, -284264849/1000000000⟩
def contact2787 : RatBall := localContactBall tau2787 center2787
def work2787 : RoundedTauEval :=
  evalTau precision tau2787 contact2787 logTwoBall

theorem center_sq2787 : (center2787.re : ℝ)^2 +
    (center2787.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2787]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2787 : work2787.theta.ok = true ∧
    work2787.jac.invOK = true ∧ acceptsUnitSq work2787.out = true := by
  norm_num [work2787, contact2787, tau2787, center2787, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2787 : CellCertificate where
  tauBall := tau2787
  contactCenter := center2787
  contactBall := contact2787
  work := work2787
  center_sq := center_sq2787
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2787.1
  jac_ok := checks2787.2.1
  accepted := checks2787.2.2

def tau2788 : RatBall :=
  ⟨⟨-47/640, -247/640⟩, 3/1280⟩
def center2788 : GaussianRat :=
  ⟨-59976659/1000000000, -70167217/250000000⟩
def contact2788 : RatBall := localContactBall tau2788 center2788
def work2788 : RoundedTauEval :=
  evalTau precision tau2788 contact2788 logTwoBall

theorem center_sq2788 : (center2788.re : ℝ)^2 +
    (center2788.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2788]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2788 : work2788.theta.ok = true ∧
    work2788.jac.invOK = true ∧ acceptsUnitSq work2788.out = true := by
  norm_num [work2788, contact2788, tau2788, center2788, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2788 : CellCertificate where
  tauBall := tau2788
  contactCenter := center2788
  contactBall := contact2788
  work := work2788
  center_sq := center_sq2788
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2788.1
  jac_ok := checks2788.2.1
  accepted := checks2788.2.2

def tau2789 : RatBall :=
  ⟨⟨-9/128, -247/640⟩, 3/1280⟩
def center2789 : GaussianRat :=
  ⟨-2872117/50000000, -14041993/50000000⟩
def contact2789 : RatBall := localContactBall tau2789 center2789
def work2789 : RoundedTauEval :=
  evalTau precision tau2789 contact2789 logTwoBall

theorem center_sq2789 : (center2789.re : ℝ)^2 +
    (center2789.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2789]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2789 : work2789.theta.ok = true ∧
    work2789.jac.invOK = true ∧ acceptsUnitSq work2789.out = true := by
  norm_num [work2789, contact2789, tau2789, center2789, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2789 : CellCertificate where
  tauBall := tau2789
  contactCenter := center2789
  contactBall := contact2789
  work := work2789
  center_sq := center_sq2789
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2789.1
  jac_ok := checks2789.2.1
  accepted := checks2789.2.2

def tau2790 : RatBall :=
  ⟨⟨-47/640, -49/128⟩, 3/1280⟩
def center2790 : GaussianRat :=
  ⟨-2392131/40000000, -55627861/200000000⟩
def contact2790 : RatBall := localContactBall tau2790 center2790
def work2790 : RoundedTauEval :=
  evalTau precision tau2790 contact2790 logTwoBall

theorem center_sq2790 : (center2790.re : ℝ)^2 +
    (center2790.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2790]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2790 : work2790.theta.ok = true ∧
    work2790.jac.invOK = true ∧ acceptsUnitSq work2790.out = true := by
  norm_num [work2790, contact2790, tau2790, center2790, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2790 : CellCertificate where
  tauBall := tau2790
  contactCenter := center2790
  contactBall := contact2790
  work := work2790
  center_sq := center_sq2790
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2790.1
  jac_ok := checks2790.2.1
  accepted := checks2790.2.2

def tau2791 : RatBall :=
  ⟨⟨-9/128, -49/128⟩, 3/1280⟩
def center2791 : GaussianRat :=
  ⟨-57276093/1000000000, -139153977/500000000⟩
def contact2791 : RatBall := localContactBall tau2791 center2791
def work2791 : RoundedTauEval :=
  evalTau precision tau2791 contact2791 logTwoBall

theorem center_sq2791 : (center2791.re : ℝ)^2 +
    (center2791.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2791]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2791 : work2791.theta.ok = true ∧
    work2791.jac.invOK = true ∧ acceptsUnitSq work2791.out = true := by
  norm_num [work2791, contact2791, tau2791, center2791, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2791 : CellCertificate where
  tauBall := tau2791
  contactCenter := center2791
  contactBall := contact2791
  work := work2791
  center_sq := center_sq2791
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2791.1
  jac_ok := checks2791.2.1
  accepted := checks2791.2.2

def cells : List CellCertificate := [cell2784, cell2785, cell2786, cell2787, cell2788, cell2789, cell2790, cell2791]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348
