import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2848 : RatBall :=
  ⟨⟨-23/640, -247/640⟩, 3/1280⟩
def center2848 : GaussianRat :=
  ⟨-1839637/62500000, -141119723/500000000⟩
def contact2848 : RatBall := localContactBall tau2848 center2848
def work2848 : RoundedTauEval :=
  evalTau precision tau2848 contact2848 logTwoBall

theorem center_sq2848 : (center2848.re : ℝ)^2 +
    (center2848.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2848]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2848 : work2848.theta.ok = true ∧
    work2848.jac.invOK = true ∧ acceptsUnitSq work2848.out = true := by
  norm_num [work2848, contact2848, tau2848, center2848, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2848 : CellCertificate where
  tauBall := tau2848
  contactCenter := center2848
  contactBall := contact2848
  work := work2848
  center_sq := center_sq2848
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2848.1
  jac_ok := checks2848.2.1
  accepted := checks2848.2.2

def tau2849 : RatBall :=
  ⟨⟨-21/640, -247/640⟩, 3/1280⟩
def center2849 : GaussianRat :=
  ⟨-26878737/1000000000, -282322297/1000000000⟩
def contact2849 : RatBall := localContactBall tau2849 center2849
def work2849 : RoundedTauEval :=
  evalTau precision tau2849 contact2849 logTwoBall

theorem center_sq2849 : (center2849.re : ℝ)^2 +
    (center2849.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2849]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2849 : work2849.theta.ok = true ∧
    work2849.jac.invOK = true ∧ acceptsUnitSq work2849.out = true := by
  norm_num [work2849, contact2849, tau2849, center2849, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2849 : CellCertificate where
  tauBall := tau2849
  contactCenter := center2849
  contactBall := contact2849
  work := work2849
  center_sq := center_sq2849
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2849.1
  jac_ok := checks2849.2.1
  accepted := checks2849.2.2

def tau2850 : RatBall :=
  ⟨⟨-23/640, -49/128⟩, 3/1280⟩
def center2850 : GaussianRat :=
  ⟨-7337051/250000000, -279688291/1000000000⟩
def contact2850 : RatBall := localContactBall tau2850 center2850
def work2850 : RoundedTauEval :=
  evalTau precision tau2850 contact2850 logTwoBall

theorem center_sq2850 : (center2850.re : ℝ)^2 +
    (center2850.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2850]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2850 : work2850.theta.ok = true ∧
    work2850.jac.invOK = true ∧ acceptsUnitSq work2850.out = true := by
  norm_num [work2850, contact2850, tau2850, center2850, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2850 : CellCertificate where
  tauBall := tau2850
  contactCenter := center2850
  contactBall := contact2850
  work := work2850
  center_sq := center_sq2850
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2850.1
  jac_ok := checks2850.2.1
  accepted := checks2850.2.2

def tau2851 : RatBall :=
  ⟨⟨-21/640, -49/128⟩, 3/1280⟩
def center2851 : GaussianRat :=
  ⟨-6700043/250000000, -139884999/500000000⟩
def contact2851 : RatBall := localContactBall tau2851 center2851
def work2851 : RoundedTauEval :=
  evalTau precision tau2851 contact2851 logTwoBall

theorem center_sq2851 : (center2851.re : ℝ)^2 +
    (center2851.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2851]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2851 : work2851.theta.ok = true ∧
    work2851.jac.invOK = true ∧ acceptsUnitSq work2851.out = true := by
  norm_num [work2851, contact2851, tau2851, center2851, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2851 : CellCertificate where
  tauBall := tau2851
  contactCenter := center2851
  contactBall := contact2851
  work := work2851
  center_sq := center_sq2851
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2851.1
  jac_ok := checks2851.2.1
  accepted := checks2851.2.2

def tau2852 : RatBall :=
  ⟨⟨-3/128, -51/128⟩, 3/1280⟩
def center2852 : GaussianRat :=
  ⟨-60747/3125000, -58564523/200000000⟩
def contact2852 : RatBall := localContactBall tau2852 center2852
def work2852 : RoundedTauEval :=
  evalTau precision tau2852 contact2852 logTwoBall

theorem center_sq2852 : (center2852.re : ℝ)^2 +
    (center2852.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2852]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2852 : work2852.theta.ok = true ∧
    work2852.jac.invOK = true ∧ acceptsUnitSq work2852.out = true := by
  norm_num [work2852, contact2852, tau2852, center2852, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2852 : CellCertificate where
  tauBall := tau2852
  contactCenter := center2852
  contactBall := contact2852
  work := work2852
  center_sq := center_sq2852
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2852.1
  jac_ok := checks2852.2.1
  accepted := checks2852.2.2

def tau2853 : RatBall :=
  ⟨⟨-13/640, -51/128⟩, 3/1280⟩
def center2853 : GaussianRat :=
  ⟨-3369771/200000000, -146439243/500000000⟩
def contact2853 : RatBall := localContactBall tau2853 center2853
def work2853 : RoundedTauEval :=
  evalTau precision tau2853 contact2853 logTwoBall

theorem center_sq2853 : (center2853.re : ℝ)^2 +
    (center2853.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2853]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2853 : work2853.theta.ok = true ∧
    work2853.jac.invOK = true ∧ acceptsUnitSq work2853.out = true := by
  norm_num [work2853, contact2853, tau2853, center2853, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2853 : CellCertificate where
  tauBall := tau2853
  contactCenter := center2853
  contactBall := contact2853
  work := work2853
  center_sq := center_sq2853
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2853.1
  jac_ok := checks2853.2.1
  accepted := checks2853.2.2

def tau2854 : RatBall :=
  ⟨⟨-3/128, -253/640⟩, 3/1280⟩
def center2854 : GaussianRat :=
  ⟨-19379607/1000000000, -58047357/200000000⟩
def contact2854 : RatBall := localContactBall tau2854 center2854
def work2854 : RoundedTauEval :=
  evalTau precision tau2854 contact2854 logTwoBall

theorem center_sq2854 : (center2854.re : ℝ)^2 +
    (center2854.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2854]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2854 : work2854.theta.ok = true ∧
    work2854.jac.invOK = true ∧ acceptsUnitSq work2854.out = true := by
  norm_num [work2854, contact2854, tau2854, center2854, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2854 : CellCertificate where
  tauBall := tau2854
  contactCenter := center2854
  contactBall := contact2854
  work := work2854
  center_sq := center_sq2854
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2854.1
  jac_ok := checks2854.2.1
  accepted := checks2854.2.2

def tau2855 : RatBall :=
  ⟨⟨-13/640, -253/640⟩, 3/1280⟩
def center2855 : GaussianRat :=
  ⟨-16797323/1000000000, -290291883/1000000000⟩
def contact2855 : RatBall := localContactBall tau2855 center2855
def work2855 : RoundedTauEval :=
  evalTau precision tau2855 contact2855 logTwoBall

theorem center_sq2855 : (center2855.re : ℝ)^2 +
    (center2855.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2855]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2855 : work2855.theta.ok = true ∧
    work2855.jac.invOK = true ∧ acceptsUnitSq work2855.out = true := by
  norm_num [work2855, contact2855, tau2855, center2855, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2855 : CellCertificate where
  tauBall := tau2855
  contactCenter := center2855
  contactBall := contact2855
  work := work2855
  center_sq := center_sq2855
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2855.1
  jac_ok := checks2855.2.1
  accepted := checks2855.2.2

def cells : List CellCertificate := [cell2848, cell2849, cell2850, cell2851, cell2852, cell2853, cell2854, cell2855]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356
