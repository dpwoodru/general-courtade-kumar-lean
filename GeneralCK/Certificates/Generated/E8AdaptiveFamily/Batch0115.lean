import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0920 : RatBall :=
  ⟨⟨-27/160, 47/160⟩, 3/320⟩
def center0920 : GaussianRat :=
  ⟨-31652671/250000000, 101529593/500000000⟩
def contact0920 : RatBall := localContactBall tau0920 center0920
def work0920 : RoundedTauEval :=
  evalTau precision tau0920 contact0920 logTwoBall

theorem center_sq0920 : (center0920.re : ℝ)^2 +
    (center0920.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0920]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0920 : work0920.theta.ok = true ∧
    work0920.jac.invOK = true ∧ acceptsUnitSq work0920.out = true := by
  norm_num [work0920, contact0920, tau0920, center0920, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0920 : CellCertificate where
  tauBall := tau0920
  contactCenter := center0920
  contactBall := contact0920
  work := work0920
  center_sq := center_sq0920
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0920.1
  jac_ok := checks0920.2.1
  accepted := checks0920.2.2

def tau0921 : RatBall :=
  ⟨⟨-5/32, 47/160⟩, 3/320⟩
def center0921 : GaussianRat :=
  ⟨-58736127/500000000, 40804889/200000000⟩
def contact0921 : RatBall := localContactBall tau0921 center0921
def work0921 : RoundedTauEval :=
  evalTau precision tau0921 contact0921 logTwoBall

theorem center_sq0921 : (center0921.re : ℝ)^2 +
    (center0921.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0921]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0921 : work0921.theta.ok = true ∧
    work0921.jac.invOK = true ∧ acceptsUnitSq work0921.out = true := by
  norm_num [work0921, contact0921, tau0921, center0921, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0921 : CellCertificate where
  tauBall := tau0921
  contactCenter := center0921
  contactBall := contact0921
  work := work0921
  center_sq := center_sq0921
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0921.1
  jac_ok := checks0921.2.1
  accepted := checks0921.2.2

def tau0922 : RatBall :=
  ⟨⟨-23/160, 41/160⟩, 3/320⟩
def center0922 : GaussianRat :=
  ⟨-105897059/1000000000, 22194707/125000000⟩
def contact0922 : RatBall := localContactBall tau0922 center0922
def work0922 : RoundedTauEval :=
  evalTau precision tau0922 contact0922 logTwoBall

theorem center_sq0922 : (center0922.re : ℝ)^2 +
    (center0922.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0922]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0922 : work0922.theta.ok = true ∧
    work0922.jac.invOK = true ∧ acceptsUnitSq work0922.out = true := by
  norm_num [work0922, contact0922, tau0922, center0922, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0922 : CellCertificate where
  tauBall := tau0922
  contactCenter := center0922
  contactBall := contact0922
  work := work0922
  center_sq := center_sq0922
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0922.1
  jac_ok := checks0922.2.1
  accepted := checks0922.2.2

def tau0923 : RatBall :=
  ⟨⟨-21/160, 41/160⟩, 3/320⟩
def center0923 : GaussianRat :=
  ⟨-96843181/1000000000, 5570429/31250000⟩
def contact0923 : RatBall := localContactBall tau0923 center0923
def work0923 : RoundedTauEval :=
  evalTau precision tau0923 contact0923 logTwoBall

theorem center_sq0923 : (center0923.re : ℝ)^2 +
    (center0923.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0923]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0923 : work0923.theta.ok = true ∧
    work0923.jac.invOK = true ∧ acceptsUnitSq work0923.out = true := by
  norm_num [work0923, contact0923, tau0923, center0923, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0923 : CellCertificate where
  tauBall := tau0923
  contactCenter := center0923
  contactBall := contact0923
  work := work0923
  center_sq := center_sq0923
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0923.1
  jac_ok := checks0923.2.1
  accepted := checks0923.2.2

def tau0924 : RatBall :=
  ⟨⟨-23/160, 43/160⟩, 3/320⟩
def center0924 : GaussianRat :=
  ⟨-106644393/1000000000, 93309307/500000000⟩
def contact0924 : RatBall := localContactBall tau0924 center0924
def work0924 : RoundedTauEval :=
  evalTau precision tau0924 contact0924 logTwoBall

theorem center_sq0924 : (center0924.re : ℝ)^2 +
    (center0924.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0924]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0924 : work0924.theta.ok = true ∧
    work0924.jac.invOK = true ∧ acceptsUnitSq work0924.out = true := by
  norm_num [work0924, contact0924, tau0924, center0924, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0924 : CellCertificate where
  tauBall := tau0924
  contactCenter := center0924
  contactBall := contact0924
  work := work0924
  center_sq := center_sq0924
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0924.1
  jac_ok := checks0924.2.1
  accepted := checks0924.2.2

def tau0925 : RatBall :=
  ⟨⟨-21/160, 43/160⟩, 3/320⟩
def center0925 : GaussianRat :=
  ⟨-1523927/15625000, 46839637/250000000⟩
def contact0925 : RatBall := localContactBall tau0925 center0925
def work0925 : RoundedTauEval :=
  evalTau precision tau0925 contact0925 logTwoBall

theorem center_sq0925 : (center0925.re : ℝ)^2 +
    (center0925.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0925]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0925 : work0925.theta.ok = true ∧
    work0925.jac.invOK = true ∧ acceptsUnitSq work0925.out = true := by
  norm_num [work0925, contact0925, tau0925, center0925, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0925 : CellCertificate where
  tauBall := tau0925
  contactCenter := center0925
  contactBall := contact0925
  work := work0925
  center_sq := center_sq0925
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0925.1
  jac_ok := checks0925.2.1
  accepted := checks0925.2.2

def tau0926 : RatBall :=
  ⟨⟨-19/160, 41/160⟩, 3/320⟩
def center0926 : GaussianRat :=
  ⟨-43873979/500000000, 35778323/200000000⟩
def contact0926 : RatBall := localContactBall tau0926 center0926
def work0926 : RoundedTauEval :=
  evalTau precision tau0926 contact0926 logTwoBall

theorem center_sq0926 : (center0926.re : ℝ)^2 +
    (center0926.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0926]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0926 : work0926.theta.ok = true ∧
    work0926.jac.invOK = true ∧ acceptsUnitSq work0926.out = true := by
  norm_num [work0926, contact0926, tau0926, center0926, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0926 : CellCertificate where
  tauBall := tau0926
  contactCenter := center0926
  contactBall := contact0926
  work := work0926
  center_sq := center_sq0926
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0926.1
  jac_ok := checks0926.2.1
  accepted := checks0926.2.2

def tau0927 : RatBall :=
  ⟨⟨-17/160, 41/160⟩, 3/320⟩
def center0927 : GaussianRat :=
  ⟨-1572299/20000000, 179469913/1000000000⟩
def contact0927 : RatBall := localContactBall tau0927 center0927
def work0927 : RoundedTauEval :=
  evalTau precision tau0927 contact0927 logTwoBall

theorem center_sq0927 : (center0927.re : ℝ)^2 +
    (center0927.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0927]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0927 : work0927.theta.ok = true ∧
    work0927.jac.invOK = true ∧ acceptsUnitSq work0927.out = true := by
  norm_num [work0927, contact0927, tau0927, center0927, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0927 : CellCertificate where
  tauBall := tau0927
  contactCenter := center0927
  contactBall := contact0927
  work := work0927
  center_sq := center_sq0927
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0927.1
  jac_ok := checks0927.2.1
  accepted := checks0927.2.2

def cells : List CellCertificate := [cell0920, cell0921, cell0922, cell0923, cell0924, cell0925, cell0926, cell0927]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115
