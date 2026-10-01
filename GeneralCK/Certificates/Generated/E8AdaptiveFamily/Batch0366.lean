import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2928 : RatBall :=
  ⟨⟨21/640, -251/640⟩, 3/1280⟩
def center2928 : GaussianRat :=
  ⟨1689949/62500000, -143724721/500000000⟩
def contact2928 : RatBall := localContactBall tau2928 center2928
def work2928 : RoundedTauEval :=
  evalTau precision tau2928 contact2928 logTwoBall

theorem center_sq2928 : (center2928.re : ℝ)^2 +
    (center2928.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2928]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2928 : work2928.theta.ok = true ∧
    work2928.jac.invOK = true ∧ acceptsUnitSq work2928.out = true := by
  norm_num [work2928, contact2928, tau2928, center2928, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2928 : CellCertificate where
  tauBall := tau2928
  contactCenter := center2928
  contactBall := contact2928
  work := work2928
  center_sq := center_sq2928
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2928.1
  jac_ok := checks2928.2.1
  accepted := checks2928.2.2

def tau2929 : RatBall :=
  ⟨⟨23/640, -251/640⟩, 3/1280⟩
def center2929 : GaussianRat :=
  ⟨14804897/500000000, -8980133/31250000⟩
def contact2929 : RatBall := localContactBall tau2929 center2929
def work2929 : RoundedTauEval :=
  evalTau precision tau2929 contact2929 logTwoBall

theorem center_sq2929 : (center2929.re : ℝ)^2 +
    (center2929.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2929]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2929 : work2929.theta.ok = true ∧
    work2929.jac.invOK = true ∧ acceptsUnitSq work2929.out = true := by
  norm_num [work2929, contact2929, tau2929, center2929, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2929 : CellCertificate where
  tauBall := tau2929
  contactCenter := center2929
  contactBall := contact2929
  work := work2929
  center_sq := center_sq2929
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2929.1
  jac_ok := checks2929.2.1
  accepted := checks2929.2.2

def tau2930 : RatBall :=
  ⟨⟨21/640, -249/640⟩, 3/1280⟩
def center2930 : GaussianRat :=
  ⟨26958403/1000000000, -284882077/1000000000⟩
def contact2930 : RatBall := localContactBall tau2930 center2930
def work2930 : RoundedTauEval :=
  evalTau precision tau2930 contact2930 logTwoBall

theorem center_sq2930 : (center2930.re : ℝ)^2 +
    (center2930.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2930]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2930 : work2930.theta.ok = true ∧
    work2930.jac.invOK = true ∧ acceptsUnitSq work2930.out = true := by
  norm_num [work2930, contact2930, tau2930, center2930, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2930 : CellCertificate where
  tauBall := tau2930
  contactCenter := center2930
  contactBall := contact2930
  work := work2930
  center_sq := center_sq2930
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2930.1
  jac_ok := checks2930.2.1
  accepted := checks2930.2.2

def tau2931 : RatBall :=
  ⟨⟨23/640, -249/640⟩, 3/1280⟩
def center2931 : GaussianRat :=
  ⟨29521383/1000000000, -142399033/500000000⟩
def contact2931 : RatBall := localContactBall tau2931 center2931
def work2931 : RoundedTauEval :=
  evalTau precision tau2931 contact2931 logTwoBall

theorem center_sq2931 : (center2931.re : ℝ)^2 +
    (center2931.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2931]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2931 : work2931.theta.ok = true ∧
    work2931.jac.invOK = true ∧ acceptsUnitSq work2931.out = true := by
  norm_num [work2931, contact2931, tau2931, center2931, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2931 : CellCertificate where
  tauBall := tau2931
  contactCenter := center2931
  contactBall := contact2931
  work := work2931
  center_sq := center_sq2931
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2931.1
  jac_ok := checks2931.2.1
  accepted := checks2931.2.2

def tau2932 : RatBall :=
  ⟨⟨5/128, -51/128⟩, 3/1280⟩
def center2932 : GaussianRat :=
  ⟨32375263/1000000000, -292424289/1000000000⟩
def contact2932 : RatBall := localContactBall tau2932 center2932
def work2932 : RoundedTauEval :=
  evalTau precision tau2932 contact2932 logTwoBall

theorem center_sq2932 : (center2932.re : ℝ)^2 +
    (center2932.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2932]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2932 : work2932.theta.ok = true ∧
    work2932.jac.invOK = true ∧ acceptsUnitSq work2932.out = true := by
  norm_num [work2932, contact2932, tau2932, center2932, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2932 : CellCertificate where
  tauBall := tau2932
  contactCenter := center2932
  contactBall := contact2932
  work := work2932
  center_sq := center_sq2932
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2932.1
  jac_ok := checks2932.2.1
  accepted := checks2932.2.2

def tau2933 : RatBall :=
  ⟨⟨27/640, -51/128⟩, 3/1280⟩
def center2933 : GaussianRat :=
  ⟨34958801/1000000000, -14616047/50000000⟩
def contact2933 : RatBall := localContactBall tau2933 center2933
def work2933 : RoundedTauEval :=
  evalTau precision tau2933 contact2933 logTwoBall

theorem center_sq2933 : (center2933.re : ℝ)^2 +
    (center2933.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2933]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2933 : work2933.theta.ok = true ∧
    work2933.jac.invOK = true ∧ acceptsUnitSq work2933.out = true := by
  norm_num [work2933, contact2933, tau2933, center2933, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2933 : CellCertificate where
  tauBall := tau2933
  contactCenter := center2933
  contactBall := contact2933
  work := work2933
  center_sq := center_sq2933
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2933.1
  jac_ok := checks2933.2.1
  accepted := checks2933.2.2

def tau2934 : RatBall :=
  ⟨⟨5/128, -253/640⟩, 3/1280⟩
def center2934 : GaussianRat :=
  ⟨16138267/500000000, -7246099/25000000⟩
def contact2934 : RatBall := localContactBall tau2934 center2934
def work2934 : RoundedTauEval :=
  evalTau precision tau2934 contact2934 logTwoBall

theorem center_sq2934 : (center2934.re : ℝ)^2 +
    (center2934.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2934]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2934 : work2934.theta.ok = true ∧
    work2934.jac.invOK = true ∧ acceptsUnitSq work2934.out = true := by
  norm_num [work2934, contact2934, tau2934, center2934, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2934 : CellCertificate where
  tauBall := tau2934
  contactCenter := center2934
  contactBall := contact2934
  work := work2934
  center_sq := center_sq2934
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2934.1
  jac_ok := checks2934.2.1
  accepted := checks2934.2.2

def tau2935 : RatBall :=
  ⟨⟨27/640, -253/640⟩, 3/1280⟩
def center2935 : GaussianRat :=
  ⟨6970453/200000000, -289742037/1000000000⟩
def contact2935 : RatBall := localContactBall tau2935 center2935
def work2935 : RoundedTauEval :=
  evalTau precision tau2935 contact2935 logTwoBall

theorem center_sq2935 : (center2935.re : ℝ)^2 +
    (center2935.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2935]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2935 : work2935.theta.ok = true ∧
    work2935.jac.invOK = true ∧ acceptsUnitSq work2935.out = true := by
  norm_num [work2935, contact2935, tau2935, center2935, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2935 : CellCertificate where
  tauBall := tau2935
  contactCenter := center2935
  contactBall := contact2935
  work := work2935
  center_sq := center_sq2935
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2935.1
  jac_ok := checks2935.2.1
  accepted := checks2935.2.2

def cells : List CellCertificate := [cell2928, cell2929, cell2930, cell2931, cell2932, cell2933, cell2934, cell2935]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366
