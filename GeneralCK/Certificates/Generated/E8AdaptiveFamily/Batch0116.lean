import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0928 : RatBall :=
  ⟨⟨-19/160, 43/160⟩, 3/320⟩
def center0928 : GaussianRat :=
  ⟨-88375401/1000000000, 188036739/1000000000⟩
def contact0928 : RatBall := localContactBall tau0928 center0928
def work0928 : RoundedTauEval :=
  evalTau precision tau0928 contact0928 logTwoBall

theorem center_sq0928 : (center0928.re : ℝ)^2 +
    (center0928.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0928]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0928 : work0928.theta.ok = true ∧
    work0928.jac.invOK = true ∧ acceptsUnitSq work0928.out = true := by
  norm_num [work0928, contact0928, tau0928, center0928, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0928 : CellCertificate where
  tauBall := tau0928
  contactCenter := center0928
  contactBall := contact0928
  work := work0928
  center_sq := center_sq0928
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0928.1
  jac_ok := checks0928.2.1
  accepted := checks0928.2.2

def tau0929 : RatBall :=
  ⟨⟨-17/160, 43/160⟩, 3/320⟩
def center0929 : GaussianRat :=
  ⟨-39590143/500000000, 47162917/250000000⟩
def contact0929 : RatBall := localContactBall tau0929 center0929
def work0929 : RoundedTauEval :=
  evalTau precision tau0929 contact0929 logTwoBall

theorem center_sq0929 : (center0929.re : ℝ)^2 +
    (center0929.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0929]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0929 : work0929.theta.ok = true ∧
    work0929.jac.invOK = true ∧ acceptsUnitSq work0929.out = true := by
  norm_num [work0929, contact0929, tau0929, center0929, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0929 : CellCertificate where
  tauBall := tau0929
  contactCenter := center0929
  contactBall := contact0929
  work := work0929
  center_sq := center_sq0929
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0929.1
  jac_ok := checks0929.2.1
  accepted := checks0929.2.2

def tau0930 : RatBall :=
  ⟨⟨-23/160, 9/32⟩, 3/320⟩
def center0930 : GaussianRat :=
  ⟨-107438161/1000000000, 195739697/1000000000⟩
def contact0930 : RatBall := localContactBall tau0930 center0930
def work0930 : RoundedTauEval :=
  evalTau precision tau0930 contact0930 logTwoBall

theorem center_sq0930 : (center0930.re : ℝ)^2 +
    (center0930.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0930]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0930 : work0930.theta.ok = true ∧
    work0930.jac.invOK = true ∧ acceptsUnitSq work0930.out = true := by
  norm_num [work0930, contact0930, tau0930, center0930, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0930 : CellCertificate where
  tauBall := tau0930
  contactCenter := center0930
  contactBall := contact0930
  work := work0930
  center_sq := center_sq0930
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0930.1
  jac_ok := checks0930.2.1
  accepted := checks0930.2.2

def tau0931 : RatBall :=
  ⟨⟨-21/160, 9/32⟩, 3/320⟩
def center0931 : GaussianRat :=
  ⟨-2456559/25000000, 19652513/100000000⟩
def contact0931 : RatBall := localContactBall tau0931 center0931
def work0931 : RoundedTauEval :=
  evalTau precision tau0931 contact0931 logTwoBall

theorem center_sq0931 : (center0931.re : ℝ)^2 +
    (center0931.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0931]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0931 : work0931.theta.ok = true ∧
    work0931.jac.invOK = true ∧ acceptsUnitSq work0931.out = true := by
  norm_num [work0931, contact0931, tau0931, center0931, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0931 : CellCertificate where
  tauBall := tau0931
  contactCenter := center0931
  contactBall := contact0931
  work := work0931
  center_sq := center_sq0931
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0931.1
  jac_ok := checks0931.2.1
  accepted := checks0931.2.2

def tau0932 : RatBall :=
  ⟨⟨-23/160, 47/160⟩, 3/320⟩
def center0932 : GaussianRat :=
  ⟨-108280123/1000000000, 204924443/1000000000⟩
def contact0932 : RatBall := localContactBall tau0932 center0932
def work0932 : RoundedTauEval :=
  evalTau precision tau0932 contact0932 logTwoBall

theorem center_sq0932 : (center0932.re : ℝ)^2 +
    (center0932.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0932]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0932 : work0932.theta.ok = true ∧
    work0932.jac.invOK = true ∧ acceptsUnitSq work0932.out = true := by
  norm_num [work0932, contact0932, tau0932, center0932, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0932 : CellCertificate where
  tauBall := tau0932
  contactCenter := center0932
  contactBall := contact0932
  work := work0932
  center_sq := center_sq0932
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0932.1
  jac_ok := checks0932.2.1
  accepted := checks0932.2.2

def tau0933 : RatBall :=
  ⟨⟨-21/160, 47/160⟩, 3/320⟩
def center0933 : GaussianRat :=
  ⟨-618987/6250000, 102878573/500000000⟩
def contact0933 : RatBall := localContactBall tau0933 center0933
def work0933 : RoundedTauEval :=
  evalTau precision tau0933 contact0933 logTwoBall

theorem center_sq0933 : (center0933.re : ℝ)^2 +
    (center0933.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0933]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0933 : work0933.theta.ok = true ∧
    work0933.jac.invOK = true ∧ acceptsUnitSq work0933.out = true := by
  norm_num [work0933, contact0933, tau0933, center0933, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0933 : CellCertificate where
  tauBall := tau0933
  contactCenter := center0933
  contactBall := contact0933
  work := work0933
  center_sq := center_sq0933
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0933.1
  jac_ok := checks0933.2.1
  accepted := checks0933.2.2

def tau0934 : RatBall :=
  ⟨⟨-19/160, 9/32⟩, 3/320⟩
def center0934 : GaussianRat :=
  ⟨-22260513/250000000, 49311287/250000000⟩
def contact0934 : RatBall := localContactBall tau0934 center0934
def work0934 : RoundedTauEval :=
  evalTau precision tau0934 contact0934 logTwoBall

theorem center_sq0934 : (center0934.re : ℝ)^2 +
    (center0934.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0934]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0934 : work0934.theta.ok = true ∧
    work0934.jac.invOK = true ∧ acceptsUnitSq work0934.out = true := by
  norm_num [work0934, contact0934, tau0934, center0934, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0934 : CellCertificate where
  tauBall := tau0934
  contactCenter := center0934
  contactBall := contact0934
  work := work0934
  center_sq := center_sq0934
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0934.1
  jac_ok := checks0934.2.1
  accepted := checks0934.2.2

def tau0935 : RatBall :=
  ⟨⟨-17/160, 9/32⟩, 3/320⟩
def center0935 : GaussianRat :=
  ⟨-19945259/250000000, 39579621/200000000⟩
def contact0935 : RatBall := localContactBall tau0935 center0935
def work0935 : RoundedTauEval :=
  evalTau precision tau0935 contact0935 logTwoBall

theorem center_sq0935 : (center0935.re : ℝ)^2 +
    (center0935.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0935]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0935 : work0935.theta.ok = true ∧
    work0935.jac.invOK = true ∧ acceptsUnitSq work0935.out = true := by
  norm_num [work0935, contact0935, tau0935, center0935, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0935 : CellCertificate where
  tauBall := tau0935
  contactCenter := center0935
  contactBall := contact0935
  work := work0935
  center_sq := center_sq0935
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0935.1
  jac_ok := checks0935.2.1
  accepted := checks0935.2.2

def cells : List CellCertificate := [cell0928, cell0929, cell0930, cell0931, cell0932, cell0933, cell0934, cell0935]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116
