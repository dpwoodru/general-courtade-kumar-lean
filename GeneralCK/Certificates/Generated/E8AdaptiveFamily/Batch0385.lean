import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3080 : RatBall :=
  ⟨⟨89/640, -241/640⟩, 3/1280⟩
def center3080 : GaussianRat :=
  ⟨22313823/200000000, -13406097/50000000⟩
def contact3080 : RatBall := localContactBall tau3080 center3080
def work3080 : RoundedTauEval :=
  evalTau precision tau3080 contact3080 logTwoBall

theorem center_sq3080 : (center3080.re : ℝ)^2 +
    (center3080.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3080]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3080 : work3080.theta.ok = true ∧
    work3080.jac.invOK = true ∧ acceptsUnitSq work3080.out = true := by
  norm_num [work3080, contact3080, tau3080, center3080, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3080 : CellCertificate where
  tauBall := tau3080
  contactCenter := center3080
  contactBall := contact3080
  work := work3080
  center_sq := center_sq3080
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3080.1
  jac_ok := checks3080.2.1
  accepted := checks3080.2.2

def tau3081 : RatBall :=
  ⟨⟨13/128, -239/640⟩, 3/1280⟩
def center3081 : GaussianRat :=
  ⟨81740791/1000000000, -268834717/1000000000⟩
def contact3081 : RatBall := localContactBall tau3081 center3081
def work3081 : RoundedTauEval :=
  evalTau precision tau3081 contact3081 logTwoBall

theorem center_sq3081 : (center3081.re : ℝ)^2 +
    (center3081.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3081]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3081 : work3081.theta.ok = true ∧
    work3081.jac.invOK = true ∧ acceptsUnitSq work3081.out = true := by
  norm_num [work3081, contact3081, tau3081, center3081, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3081 : CellCertificate where
  tauBall := tau3081
  contactCenter := center3081
  contactBall := contact3081
  work := work3081
  center_sq := center_sq3081
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3081.1
  jac_ok := checks3081.2.1
  accepted := checks3081.2.2

def tau3082 : RatBall :=
  ⟨⟨67/640, -239/640⟩, 3/1280⟩
def center3082 : GaussianRat :=
  ⟨5263767/62500000, -134303253/500000000⟩
def contact3082 : RatBall := localContactBall tau3082 center3082
def work3082 : RoundedTauEval :=
  evalTau precision tau3082 contact3082 logTwoBall

theorem center_sq3082 : (center3082.re : ℝ)^2 +
    (center3082.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3082]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3082 : work3082.theta.ok = true ∧
    work3082.jac.invOK = true ∧ acceptsUnitSq work3082.out = true := by
  norm_num [work3082, contact3082, tau3082, center3082, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3082 : CellCertificate where
  tauBall := tau3082
  contactCenter := center3082
  contactBall := contact3082
  work := work3082
  center_sq := center_sq3082
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3082.1
  jac_ok := checks3082.2.1
  accepted := checks3082.2.2

def tau3083 : RatBall :=
  ⟨⟨13/128, -237/640⟩, 3/1280⟩
def center3083 : GaussianRat :=
  ⟨40758673/500000000, -133178453/500000000⟩
def contact3083 : RatBall := localContactBall tau3083 center3083
def work3083 : RoundedTauEval :=
  evalTau precision tau3083 contact3083 logTwoBall

theorem center_sq3083 : (center3083.re : ℝ)^2 +
    (center3083.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3083]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3083 : work3083.theta.ok = true ∧
    work3083.jac.invOK = true ∧ acceptsUnitSq work3083.out = true := by
  norm_num [work3083, contact3083, tau3083, center3083, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3083 : CellCertificate where
  tauBall := tau3083
  contactCenter := center3083
  contactBall := contact3083
  work := work3083
  center_sq := center_sq3083
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3083.1
  jac_ok := checks3083.2.1
  accepted := checks3083.2.2

def tau3084 : RatBall :=
  ⟨⟨67/640, -237/640⟩, 3/1280⟩
def center3084 : GaussianRat :=
  ⟨20997603/250000000, -266131799/1000000000⟩
def contact3084 : RatBall := localContactBall tau3084 center3084
def work3084 : RoundedTauEval :=
  evalTau precision tau3084 contact3084 logTwoBall

theorem center_sq3084 : (center3084.re : ℝ)^2 +
    (center3084.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3084]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3084 : work3084.theta.ok = true ∧
    work3084.jac.invOK = true ∧ acceptsUnitSq work3084.out = true := by
  norm_num [work3084, contact3084, tau3084, center3084, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3084 : CellCertificate where
  tauBall := tau3084
  contactCenter := center3084
  contactBall := contact3084
  work := work3084
  center_sq := center_sq3084
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3084.1
  jac_ok := checks3084.2.1
  accepted := checks3084.2.2

def tau3085 : RatBall :=
  ⟨⟨69/640, -239/640⟩, 3/1280⟩
def center3085 : GaussianRat :=
  ⟨43348293/500000000, -268371857/1000000000⟩
def contact3085 : RatBall := localContactBall tau3085 center3085
def work3085 : RoundedTauEval :=
  evalTau precision tau3085 contact3085 logTwoBall

theorem center_sq3085 : (center3085.re : ℝ)^2 +
    (center3085.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3085]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3085 : work3085.theta.ok = true ∧
    work3085.jac.invOK = true ∧ acceptsUnitSq work3085.out = true := by
  norm_num [work3085, contact3085, tau3085, center3085, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3085 : CellCertificate where
  tauBall := tau3085
  contactCenter := center3085
  contactBall := contact3085
  work := work3085
  center_sq := center_sq3085
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3085.1
  jac_ok := checks3085.2.1
  accepted := checks3085.2.2

def tau3086 : RatBall :=
  ⟨⟨71/640, -239/640⟩, 3/1280⟩
def center3086 : GaussianRat :=
  ⟨89169649/1000000000, -67032703/250000000⟩
def contact3086 : RatBall := localContactBall tau3086 center3086
def work3086 : RoundedTauEval :=
  evalTau precision tau3086 contact3086 logTwoBall

theorem center_sq3086 : (center3086.re : ℝ)^2 +
    (center3086.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3086]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3086 : work3086.theta.ok = true ∧
    work3086.jac.invOK = true ∧ acceptsUnitSq work3086.out = true := by
  norm_num [work3086, contact3086, tau3086, center3086, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3086 : CellCertificate where
  tauBall := tau3086
  contactCenter := center3086
  contactBall := contact3086
  work := work3086
  center_sq := center_sq3086
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3086.1
  jac_ok := checks3086.2.1
  accepted := checks3086.2.2

def tau3087 : RatBall :=
  ⟨⟨69/640, -237/640⟩, 3/1280⟩
def center3087 : GaussianRat :=
  ⟨86460351/1000000000, -265900339/1000000000⟩
def contact3087 : RatBall := localContactBall tau3087 center3087
def work3087 : RoundedTauEval :=
  evalTau precision tau3087 contact3087 logTwoBall

theorem center_sq3087 : (center3087.re : ℝ)^2 +
    (center3087.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3087]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3087 : work3087.theta.ok = true ∧
    work3087.jac.invOK = true ∧ acceptsUnitSq work3087.out = true := by
  norm_num [work3087, contact3087, tau3087, center3087, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3087 : CellCertificate where
  tauBall := tau3087
  contactCenter := center3087
  contactBall := contact3087
  work := work3087
  center_sq := center_sq3087
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3087.1
  jac_ok := checks3087.2.1
  accepted := checks3087.2.2

def cells : List CellCertificate := [cell3080, cell3081, cell3082, cell3083, cell3084, cell3085, cell3086, cell3087]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385
