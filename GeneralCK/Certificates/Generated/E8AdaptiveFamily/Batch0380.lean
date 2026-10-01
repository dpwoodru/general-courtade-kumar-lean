import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3040 : RatBall :=
  ⟨⟨59/640, -243/640⟩, 3/1280⟩
def center3040 : GaussianRat :=
  ⟨74700643/1000000000, -13723671/50000000⟩
def contact3040 : RatBall := localContactBall tau3040 center3040
def work3040 : RoundedTauEval :=
  evalTau precision tau3040 contact3040 logTwoBall

theorem center_sq3040 : (center3040.re : ℝ)^2 +
    (center3040.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3040]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3040 : work3040.theta.ok = true ∧
    work3040.jac.invOK = true ∧ acceptsUnitSq work3040.out = true := by
  norm_num [work3040, contact3040, tau3040, center3040, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3040 : CellCertificate where
  tauBall := tau3040
  contactCenter := center3040
  contactBall := contact3040
  work := work3040
  center_sq := center_sq3040
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3040.1
  jac_ok := checks3040.2.1
  accepted := checks3040.2.2

def tau3041 : RatBall :=
  ⟨⟨57/640, -241/640⟩, 3/1280⟩
def center3041 : GaussianRat :=
  ⟨1439861/20000000, -68044601/250000000⟩
def contact3041 : RatBall := localContactBall tau3041 center3041
def work3041 : RoundedTauEval :=
  evalTau precision tau3041 contact3041 logTwoBall

theorem center_sq3041 : (center3041.re : ℝ)^2 +
    (center3041.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3041]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3041 : work3041.theta.ok = true ∧
    work3041.jac.invOK = true ∧ acceptsUnitSq work3041.out = true := by
  norm_num [work3041, contact3041, tau3041, center3041, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3041 : CellCertificate where
  tauBall := tau3041
  contactCenter := center3041
  contactBall := contact3041
  work := work3041
  center_sq := center_sq3041
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3041.1
  jac_ok := checks3041.2.1
  accepted := checks3041.2.2

def tau3042 : RatBall :=
  ⟨⟨59/640, -241/640⟩, 3/1280⟩
def center3042 : GaussianRat :=
  ⟨37245497/500000000, -8499173/31250000⟩
def contact3042 : RatBall := localContactBall tau3042 center3042
def work3042 : RoundedTauEval :=
  evalTau precision tau3042 contact3042 logTwoBall

theorem center_sq3042 : (center3042.re : ℝ)^2 +
    (center3042.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3042]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3042 : work3042.theta.ok = true ∧
    work3042.jac.invOK = true ∧ acceptsUnitSq work3042.out = true := by
  norm_num [work3042, contact3042, tau3042, center3042, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3042 : CellCertificate where
  tauBall := tau3042
  contactCenter := center3042
  contactBall := contact3042
  work := work3042
  center_sq := center_sq3042
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3042.1
  jac_ok := checks3042.2.1
  accepted := checks3042.2.2

def tau3043 : RatBall :=
  ⟨⟨61/640, -243/640⟩, 3/1280⟩
def center3043 : GaussianRat :=
  ⟨77202433/1000000000, -5485179/20000000⟩
def contact3043 : RatBall := localContactBall tau3043 center3043
def work3043 : RoundedTauEval :=
  evalTau precision tau3043 contact3043 logTwoBall

theorem center_sq3043 : (center3043.re : ℝ)^2 +
    (center3043.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3043]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3043 : work3043.theta.ok = true ∧
    work3043.jac.invOK = true ∧ acceptsUnitSq work3043.out = true := by
  norm_num [work3043, contact3043, tau3043, center3043, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3043 : CellCertificate where
  tauBall := tau3043
  contactCenter := center3043
  contactBall := contact3043
  work := work3043
  center_sq := center_sq3043
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3043.1
  jac_ok := checks3043.2.1
  accepted := checks3043.2.2

def tau3044 : RatBall :=
  ⟨⟨63/640, -243/640⟩, 3/1280⟩
def center3044 : GaussianRat :=
  ⟨79701237/1000000000, -274037749/1000000000⟩
def contact3044 : RatBall := localContactBall tau3044 center3044
def work3044 : RoundedTauEval :=
  evalTau precision tau3044 contact3044 logTwoBall

theorem center_sq3044 : (center3044.re : ℝ)^2 +
    (center3044.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3044]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3044 : work3044.theta.ok = true ∧
    work3044.jac.invOK = true ∧ acceptsUnitSq work3044.out = true := by
  norm_num [work3044, contact3044, tau3044, center3044, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3044 : CellCertificate where
  tauBall := tau3044
  contactCenter := center3044
  contactBall := contact3044
  work := work3044
  center_sq := center_sq3044
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3044.1
  jac_ok := checks3044.2.1
  accepted := checks3044.2.2

def tau3045 : RatBall :=
  ⟨⟨61/640, -241/640⟩, 3/1280⟩
def center3045 : GaussianRat :=
  ⟨38493039/500000000, -67940497/250000000⟩
def contact3045 : RatBall := localContactBall tau3045 center3045
def work3045 : RoundedTauEval :=
  evalTau precision tau3045 contact3045 logTwoBall

theorem center_sq3045 : (center3045.re : ℝ)^2 +
    (center3045.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3045]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3045 : work3045.theta.ok = true ∧
    work3045.jac.invOK = true ∧ acceptsUnitSq work3045.out = true := by
  norm_num [work3045, contact3045, tau3045, center3045, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3045 : CellCertificate where
  tauBall := tau3045
  contactCenter := center3045
  contactBall := contact3045
  work := work3045
  center_sq := center_sq3045
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3045.1
  jac_ok := checks3045.2.1
  accepted := checks3045.2.2

def tau3046 : RatBall :=
  ⟨⟨63/640, -241/640⟩, 3/1280⟩
def center3046 : GaussianRat :=
  ⟨15895643/200000000, -271543799/1000000000⟩
def contact3046 : RatBall := localContactBall tau3046 center3046
def work3046 : RoundedTauEval :=
  evalTau precision tau3046 contact3046 logTwoBall

theorem center_sq3046 : (center3046.re : ℝ)^2 +
    (center3046.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3046]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3046 : work3046.theta.ok = true ∧
    work3046.jac.invOK = true ∧ acceptsUnitSq work3046.out = true := by
  norm_num [work3046, contact3046, tau3046, center3046, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3046 : CellCertificate where
  tauBall := tau3046
  contactCenter := center3046
  contactBall := contact3046
  work := work3046
  center_sq := center_sq3046
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3046.1
  jac_ok := checks3046.2.1
  accepted := checks3046.2.2

def tau3047 : RatBall :=
  ⟨⟨13/128, -247/640⟩, 3/1280⟩
def center3047 : GaussianRat :=
  ⟨82665793/1000000000, -278811601/1000000000⟩
def contact3047 : RatBall := localContactBall tau3047 center3047
def work3047 : RoundedTauEval :=
  evalTau precision tau3047 contact3047 logTwoBall

theorem center_sq3047 : (center3047.re : ℝ)^2 +
    (center3047.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3047]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3047 : work3047.theta.ok = true ∧
    work3047.jac.invOK = true ∧ acceptsUnitSq work3047.out = true := by
  norm_num [work3047, contact3047, tau3047, center3047, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3047 : CellCertificate where
  tauBall := tau3047
  contactCenter := center3047
  contactBall := contact3047
  work := work3047
  center_sq := center_sq3047
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3047.1
  jac_ok := checks3047.2.1
  accepted := checks3047.2.2

def cells : List CellCertificate := [cell3040, cell3041, cell3042, cell3043, cell3044, cell3045, cell3046, cell3047]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380
