import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3024 : RatBall :=
  ⟨⟨51/640, -243/640⟩, 3/1280⟩
def center3024 : GaussianRat :=
  ⟨32332713/500000000, -275263239/1000000000⟩
def contact3024 : RatBall := localContactBall tau3024 center3024
def work3024 : RoundedTauEval :=
  evalTau precision tau3024 contact3024 logTwoBall

theorem center_sq3024 : (center3024.re : ℝ)^2 +
    (center3024.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3024]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3024 : work3024.theta.ok = true ∧
    work3024.jac.invOK = true ∧ acceptsUnitSq work3024.out = true := by
  norm_num [work3024, contact3024, tau3024, center3024, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3024 : CellCertificate where
  tauBall := tau3024
  contactCenter := center3024
  contactBall := contact3024
  work := work3024
  center_sq := center_sq3024
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3024.1
  jac_ok := checks3024.2.1
  accepted := checks3024.2.2

def tau3025 : RatBall :=
  ⟨⟨49/640, -241/640⟩, 3/1280⟩
def center3025 : GaussianRat :=
  ⟨12394897/200000000, -272930361/1000000000⟩
def contact3025 : RatBall := localContactBall tau3025 center3025
def work3025 : RoundedTauEval :=
  evalTau precision tau3025 contact3025 logTwoBall

theorem center_sq3025 : (center3025.re : ℝ)^2 +
    (center3025.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3025]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3025 : work3025.theta.ok = true ∧
    work3025.jac.invOK = true ∧ acceptsUnitSq work3025.out = true := by
  norm_num [work3025, contact3025, tau3025, center3025, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3025 : CellCertificate where
  tauBall := tau3025
  contactCenter := center3025
  contactBall := contact3025
  work := work3025
  center_sq := center_sq3025
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3025.1
  jac_ok := checks3025.2.1
  accepted := checks3025.2.2

def tau3026 : RatBall :=
  ⟨⟨51/640, -241/640⟩, 3/1280⟩
def center3026 : GaussianRat :=
  ⟨16120741/250000000, -34094071/125000000⟩
def contact3026 : RatBall := localContactBall tau3026 center3026
def work3026 : RoundedTauEval :=
  evalTau precision tau3026 contact3026 logTwoBall

theorem center_sq3026 : (center3026.re : ℝ)^2 +
    (center3026.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3026]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3026 : work3026.theta.ok = true ∧
    work3026.jac.invOK = true ∧ acceptsUnitSq work3026.out = true := by
  norm_num [work3026, contact3026, tau3026, center3026, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3026 : CellCertificate where
  tauBall := tau3026
  contactCenter := center3026
  contactBall := contact3026
  work := work3026
  center_sq := center_sq3026
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3026.1
  jac_ok := checks3026.2.1
  accepted := checks3026.2.2

def tau3027 : RatBall :=
  ⟨⟨53/640, -243/640⟩, 3/1280⟩
def center3027 : GaussianRat :=
  ⟨67178257/1000000000, -137538033/500000000⟩
def contact3027 : RatBall := localContactBall tau3027 center3027
def work3027 : RoundedTauEval :=
  evalTau precision tau3027 contact3027 logTwoBall

theorem center_sq3027 : (center3027.re : ℝ)^2 +
    (center3027.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3027]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3027 : work3027.theta.ok = true ∧
    work3027.jac.invOK = true ∧ acceptsUnitSq work3027.out = true := by
  norm_num [work3027, contact3027, tau3027, center3027, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3027 : CellCertificate where
  tauBall := tau3027
  contactCenter := center3027
  contactBall := contact3027
  work := work3027
  center_sq := center_sq3027
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3027.1
  jac_ok := checks3027.2.1
  accepted := checks3027.2.2

def tau3028 : RatBall :=
  ⟨⟨11/128, -243/640⟩, 3/1280⟩
def center3028 : GaussianRat :=
  ⟨13937693/200000000, -54976403/200000000⟩
def contact3028 : RatBall := localContactBall tau3028 center3028
def work3028 : RoundedTauEval :=
  evalTau precision tau3028 contact3028 logTwoBall

theorem center_sq3028 : (center3028.re : ℝ)^2 +
    (center3028.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3028]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3028 : work3028.theta.ok = true ∧
    work3028.jac.invOK = true ∧ acceptsUnitSq work3028.out = true := by
  norm_num [work3028, contact3028, tau3028, center3028, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3028 : CellCertificate where
  tauBall := tau3028
  contactCenter := center3028
  contactBall := contact3028
  work := work3028
  center_sq := center_sq3028
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3028.1
  jac_ok := checks3028.2.1
  accepted := checks3028.2.2

def tau3029 : RatBall :=
  ⟨⟨53/640, -241/640⟩, 3/1280⟩
def center3029 : GaussianRat :=
  ⟨13397789/200000000, -54513591/200000000⟩
def contact3029 : RatBall := localContactBall tau3029 center3029
def work3029 : RoundedTauEval :=
  evalTau precision tau3029 contact3029 logTwoBall

theorem center_sq3029 : (center3029.re : ℝ)^2 +
    (center3029.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3029]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3029 : work3029.theta.ok = true ∧
    work3029.jac.invOK = true ∧ acceptsUnitSq work3029.out = true := by
  norm_num [work3029, contact3029, tau3029, center3029, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3029 : CellCertificate where
  tauBall := tau3029
  contactCenter := center3029
  contactBall := contact3029
  work := work3029
  center_sq := center_sq3029
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3029.1
  jac_ok := checks3029.2.1
  accepted := checks3029.2.2

def tau3030 : RatBall :=
  ⟨⟨11/128, -241/640⟩, 3/1280⟩
def center3030 : GaussianRat :=
  ⟨34746169/500000000, -68094139/250000000⟩
def contact3030 : RatBall := localContactBall tau3030 center3030
def work3030 : RoundedTauEval :=
  evalTau precision tau3030 contact3030 logTwoBall

theorem center_sq3030 : (center3030.re : ℝ)^2 +
    (center3030.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3030]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3030 : work3030.theta.ok = true ∧
    work3030.jac.invOK = true ∧ acceptsUnitSq work3030.out = true := by
  norm_num [work3030, contact3030, tau3030, center3030, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3030 : CellCertificate where
  tauBall := tau3030
  contactCenter := center3030
  contactBall := contact3030
  work := work3030
  center_sq := center_sq3030
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3030.1
  jac_ok := checks3030.2.1
  accepted := checks3030.2.2

def tau3031 : RatBall :=
  ⟨⟨57/640, -247/640⟩, 3/1280⟩
def center3031 : GaussianRat :=
  ⟨72610227/1000000000, -34963383/125000000⟩
def contact3031 : RatBall := localContactBall tau3031 center3031
def work3031 : RoundedTauEval :=
  evalTau precision tau3031 contact3031 logTwoBall

theorem center_sq3031 : (center3031.re : ℝ)^2 +
    (center3031.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3031]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3031 : work3031.theta.ok = true ∧
    work3031.jac.invOK = true ∧ acceptsUnitSq work3031.out = true := by
  norm_num [work3031, contact3031, tau3031, center3031, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3031 : CellCertificate where
  tauBall := tau3031
  contactCenter := center3031
  contactBall := contact3031
  work := work3031
  center_sq := center_sq3031
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3031.1
  jac_ok := checks3031.2.1
  accepted := checks3031.2.2

def cells : List CellCertificate := [cell3024, cell3025, cell3026, cell3027, cell3028, cell3029, cell3030, cell3031]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378
