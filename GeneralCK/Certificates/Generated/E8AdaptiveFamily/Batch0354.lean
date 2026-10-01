import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2832 : RatBall :=
  ⟨⟨-23/640, -251/640⟩, 3/1280⟩
def center2832 : GaussianRat :=
  ⟨-14804897/500000000, -8980133/31250000⟩
def contact2832 : RatBall := localContactBall tau2832 center2832
def work2832 : RoundedTauEval :=
  evalTau precision tau2832 contact2832 logTwoBall

theorem center_sq2832 : (center2832.re : ℝ)^2 +
    (center2832.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2832]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2832 : work2832.theta.ok = true ∧
    work2832.jac.invOK = true ∧ acceptsUnitSq work2832.out = true := by
  norm_num [work2832, contact2832, tau2832, center2832, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2832 : CellCertificate where
  tauBall := tau2832
  contactCenter := center2832
  contactBall := contact2832
  work := work2832
  center_sq := center_sq2832
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2832.1
  jac_ok := checks2832.2.1
  accepted := checks2832.2.2

def tau2833 : RatBall :=
  ⟨⟨-21/640, -251/640⟩, 3/1280⟩
def center2833 : GaussianRat :=
  ⟨-1689949/62500000, -143724721/500000000⟩
def contact2833 : RatBall := localContactBall tau2833 center2833
def work2833 : RoundedTauEval :=
  evalTau precision tau2833 contact2833 logTwoBall

theorem center_sq2833 : (center2833.re : ℝ)^2 +
    (center2833.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2833]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2833 : work2833.theta.ok = true ∧
    work2833.jac.invOK = true ∧ acceptsUnitSq work2833.out = true := by
  norm_num [work2833, contact2833, tau2833, center2833, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2833 : CellCertificate where
  tauBall := tau2833
  contactCenter := center2833
  contactBall := contact2833
  work := work2833
  center_sq := center_sq2833
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2833.1
  jac_ok := checks2833.2.1
  accepted := checks2833.2.2

def tau2834 : RatBall :=
  ⟨⟨-23/640, -249/640⟩, 3/1280⟩
def center2834 : GaussianRat :=
  ⟨-29521383/1000000000, -142399033/500000000⟩
def contact2834 : RatBall := localContactBall tau2834 center2834
def work2834 : RoundedTauEval :=
  evalTau precision tau2834 contact2834 logTwoBall

theorem center_sq2834 : (center2834.re : ℝ)^2 +
    (center2834.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2834]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2834 : work2834.theta.ok = true ∧
    work2834.jac.invOK = true ∧ acceptsUnitSq work2834.out = true := by
  norm_num [work2834, contact2834, tau2834, center2834, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2834 : CellCertificate where
  tauBall := tau2834
  contactCenter := center2834
  contactBall := contact2834
  work := work2834
  center_sq := center_sq2834
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2834.1
  jac_ok := checks2834.2.1
  accepted := checks2834.2.2

def tau2835 : RatBall :=
  ⟨⟨-21/640, -249/640⟩, 3/1280⟩
def center2835 : GaussianRat :=
  ⟨-26958403/1000000000, -284882077/1000000000⟩
def contact2835 : RatBall := localContactBall tau2835 center2835
def work2835 : RoundedTauEval :=
  evalTau precision tau2835 contact2835 logTwoBall

theorem center_sq2835 : (center2835.re : ℝ)^2 +
    (center2835.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2835]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2835 : work2835.theta.ok = true ∧
    work2835.jac.invOK = true ∧ acceptsUnitSq work2835.out = true := by
  norm_num [work2835, contact2835, tau2835, center2835, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2835 : CellCertificate where
  tauBall := tau2835
  contactCenter := center2835
  contactBall := contact2835
  work := work2835
  center_sq := center_sq2835
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2835.1
  jac_ok := checks2835.2.1
  accepted := checks2835.2.2

def tau2836 : RatBall :=
  ⟨⟨-19/640, -251/640⟩, 3/1280⟩
def center2836 : GaussianRat :=
  ⟨-12233721/500000000, -287526937/1000000000⟩
def contact2836 : RatBall := localContactBall tau2836 center2836
def work2836 : RoundedTauEval :=
  evalTau precision tau2836 contact2836 logTwoBall

theorem center_sq2836 : (center2836.re : ℝ)^2 +
    (center2836.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2836]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2836 : work2836.theta.ok = true ∧
    work2836.jac.invOK = true ∧ acceptsUnitSq work2836.out = true := by
  norm_num [work2836, contact2836, tau2836, center2836, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2836 : CellCertificate where
  tauBall := tau2836
  contactCenter := center2836
  contactBall := contact2836
  work := work2836
  center_sq := center_sq2836
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2836.1
  jac_ok := checks2836.2.1
  accepted := checks2836.2.2

def tau2837 : RatBall :=
  ⟨⟨-17/640, -251/640⟩, 3/1280⟩
def center2837 : GaussianRat :=
  ⟨-21894677/1000000000, -143798363/500000000⟩
def contact2837 : RatBall := localContactBall tau2837 center2837
def work2837 : RoundedTauEval :=
  evalTau precision tau2837 contact2837 logTwoBall

theorem center_sq2837 : (center2837.re : ℝ)^2 +
    (center2837.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2837]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2837 : work2837.theta.ok = true ∧
    work2837.jac.invOK = true ∧ acceptsUnitSq work2837.out = true := by
  norm_num [work2837, contact2837, tau2837, center2837, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2837 : CellCertificate where
  tauBall := tau2837
  contactCenter := center2837
  contactBall := contact2837
  work := work2837
  center_sq := center_sq2837
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2837.1
  jac_ok := checks2837.2.1
  accepted := checks2837.2.2

def tau2838 : RatBall :=
  ⟨⟨-19/640, -249/640⟩, 3/1280⟩
def center2838 : GaussianRat :=
  ⟨-6098577/250000000, -142479251/500000000⟩
def contact2838 : RatBall := localContactBall tau2838 center2838
def work2838 : RoundedTauEval :=
  evalTau precision tau2838 contact2838 logTwoBall

theorem center_sq2838 : (center2838.re : ℝ)^2 +
    (center2838.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2838]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2838 : work2838.theta.ok = true ∧
    work2838.jac.invOK = true ∧ acceptsUnitSq work2838.out = true := by
  norm_num [work2838, contact2838, tau2838, center2838, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2838 : CellCertificate where
  tauBall := tau2838
  contactCenter := center2838
  contactBall := contact2838
  work := work2838
  center_sq := center_sq2838
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2838.1
  jac_ok := checks2838.2.1
  accepted := checks2838.2.2

def tau2839 : RatBall :=
  ⟨⟨-17/640, -249/640⟩, 3/1280⟩
def center2839 : GaussianRat :=
  ⟨-10914601/500000000, -285027327/1000000000⟩
def contact2839 : RatBall := localContactBall tau2839 center2839
def work2839 : RoundedTauEval :=
  evalTau precision tau2839 contact2839 logTwoBall

theorem center_sq2839 : (center2839.re : ℝ)^2 +
    (center2839.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2839]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2839 : work2839.theta.ok = true ∧
    work2839.jac.invOK = true ∧ acceptsUnitSq work2839.out = true := by
  norm_num [work2839, contact2839, tau2839, center2839, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2839 : CellCertificate where
  tauBall := tau2839
  contactCenter := center2839
  contactBall := contact2839
  work := work2839
  center_sq := center_sq2839
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2839.1
  jac_ok := checks2839.2.1
  accepted := checks2839.2.2

def cells : List CellCertificate := [cell2832, cell2833, cell2834, cell2835, cell2836, cell2837, cell2838, cell2839]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354
