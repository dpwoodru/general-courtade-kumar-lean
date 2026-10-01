import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3088 : RatBall :=
  ⟨⟨71/640, -237/640⟩, 3/1280⟩
def center3088 : GaussianRat :=
  ⟨2223177/25000000, -53132513/200000000⟩
def contact3088 : RatBall := localContactBall tau3088 center3088
def work3088 : RoundedTauEval :=
  evalTau precision tau3088 contact3088 logTwoBall

theorem center_sq3088 : (center3088.re : ℝ)^2 +
    (center3088.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3088]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3088 : work3088.theta.ok = true ∧
    work3088.jac.invOK = true ∧ acceptsUnitSq work3088.out = true := by
  norm_num [work3088, contact3088, tau3088, center3088, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3088 : CellCertificate where
  tauBall := tau3088
  contactCenter := center3088
  contactBall := contact3088
  work := work3088
  center_sq := center_sq3088
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3088.1
  jac_ok := checks3088.2.1
  accepted := checks3088.2.2

def tau3089 : RatBall :=
  ⟨⟨73/640, -239/640⟩, 3/1280⟩
def center3089 : GaussianRat :=
  ⟨91639379/1000000000, -267883413/1000000000⟩
def contact3089 : RatBall := localContactBall tau3089 center3089
def work3089 : RoundedTauEval :=
  evalTau precision tau3089 contact3089 logTwoBall

theorem center_sq3089 : (center3089.re : ℝ)^2 +
    (center3089.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3089]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3089 : work3089.theta.ok = true ∧
    work3089.jac.invOK = true ∧ acceptsUnitSq work3089.out = true := by
  norm_num [work3089, contact3089, tau3089, center3089, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3089 : CellCertificate where
  tauBall := tau3089
  contactCenter := center3089
  contactBall := contact3089
  work := work3089
  center_sq := center_sq3089
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3089.1
  jac_ok := checks3089.2.1
  accepted := checks3089.2.2

def tau3090 : RatBall :=
  ⟨⟨15/128, -239/640⟩, 3/1280⟩
def center3090 : GaussianRat :=
  ⟨23526423/250000000, -133814851/500000000⟩
def contact3090 : RatBall := localContactBall tau3090 center3090
def work3090 : RoundedTauEval :=
  evalTau precision tau3090 contact3090 logTwoBall

theorem center_sq3090 : (center3090.re : ℝ)^2 +
    (center3090.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3090]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3090 : work3090.theta.ok = true ∧
    work3090.jac.invOK = true ∧ acceptsUnitSq work3090.out = true := by
  norm_num [work3090, contact3090, tau3090, center3090, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3090 : CellCertificate where
  tauBall := tau3090
  contactCenter := center3090
  contactBall := contact3090
  work := work3090
  center_sq := center_sq3090
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3090.1
  jac_ok := checks3090.2.1
  accepted := checks3090.2.2

def tau3091 : RatBall :=
  ⟨⟨73/640, -237/640⟩, 3/1280⟩
def center3091 : GaussianRat :=
  ⟨45695259/500000000, -6635463/25000000⟩
def contact3091 : RatBall := localContactBall tau3091 center3091
def work3091 : RoundedTauEval :=
  evalTau precision tau3091 contact3091 logTwoBall

theorem center_sq3091 : (center3091.re : ℝ)^2 +
    (center3091.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3091]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3091 : work3091.theta.ok = true ∧
    work3091.jac.invOK = true ∧ acceptsUnitSq work3091.out = true := by
  norm_num [work3091, contact3091, tau3091, center3091, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3091 : CellCertificate where
  tauBall := tau3091
  contactCenter := center3091
  contactBall := contact3091
  work := work3091
  center_sq := center_sq3091
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3091.1
  jac_ok := checks3091.2.1
  accepted := checks3091.2.2

def tau3092 : RatBall :=
  ⟨⟨15/128, -237/640⟩, 3/1280⟩
def center3092 : GaussianRat :=
  ⟨46925291/500000000, -53033649/200000000⟩
def contact3092 : RatBall := localContactBall tau3092 center3092
def work3092 : RoundedTauEval :=
  evalTau precision tau3092 contact3092 logTwoBall

theorem center_sq3092 : (center3092.re : ℝ)^2 +
    (center3092.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3092]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3092 : work3092.theta.ok = true ∧
    work3092.jac.invOK = true ∧ acceptsUnitSq work3092.out = true := by
  norm_num [work3092, contact3092, tau3092, center3092, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3092 : CellCertificate where
  tauBall := tau3092
  contactCenter := center3092
  contactBall := contact3092
  work := work3092
  center_sq := center_sq3092
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3092.1
  jac_ok := checks3092.2.1
  accepted := checks3092.2.2

def tau3093 : RatBall :=
  ⟨⟨77/640, -239/640⟩, 3/1280⟩
def center3093 : GaussianRat :=
  ⟨96568507/1000000000, -66842431/250000000⟩
def contact3093 : RatBall := localContactBall tau3093 center3093
def work3093 : RoundedTauEval :=
  evalTau precision tau3093 contact3093 logTwoBall

theorem center_sq3093 : (center3093.re : ℝ)^2 +
    (center3093.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3093]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3093 : work3093.theta.ok = true ∧
    work3093.jac.invOK = true ∧ acceptsUnitSq work3093.out = true := by
  norm_num [work3093, contact3093, tau3093, center3093, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3093 : CellCertificate where
  tauBall := tau3093
  contactCenter := center3093
  contactBall := contact3093
  work := work3093
  center_sq := center_sq3093
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3093.1
  jac_ok := checks3093.2.1
  accepted := checks3093.2.2

def tau3094 : RatBall :=
  ⟨⟨79/640, -239/640⟩, 3/1280⟩
def center3094 : GaussianRat :=
  ⟨99027743/1000000000, -267103523/1000000000⟩
def contact3094 : RatBall := localContactBall tau3094 center3094
def work3094 : RoundedTauEval :=
  evalTau precision tau3094 contact3094 logTwoBall

theorem center_sq3094 : (center3094.re : ℝ)^2 +
    (center3094.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3094]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3094 : work3094.theta.ok = true ∧
    work3094.jac.invOK = true ∧ acceptsUnitSq work3094.out = true := by
  norm_num [work3094, contact3094, tau3094, center3094, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3094 : CellCertificate where
  tauBall := tau3094
  contactCenter := center3094
  contactBall := contact3094
  work := work3094
  center_sq := center_sq3094
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3094.1
  jac_ok := checks3094.2.1
  accepted := checks3094.2.2

def tau3095 : RatBall :=
  ⟨⟨77/640, -237/640⟩, 3/1280⟩
def center3095 : GaussianRat :=
  ⟨96307191/1000000000, -264911783/1000000000⟩
def contact3095 : RatBall := localContactBall tau3095 center3095
def work3095 : RoundedTauEval :=
  evalTau precision tau3095 contact3095 logTwoBall

theorem center_sq3095 : (center3095.re : ℝ)^2 +
    (center3095.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3095]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3095 : work3095.theta.ok = true ∧
    work3095.jac.invOK = true ∧ acceptsUnitSq work3095.out = true := by
  norm_num [work3095, contact3095, tau3095, center3095, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3095 : CellCertificate where
  tauBall := tau3095
  contactCenter := center3095
  contactBall := contact3095
  work := work3095
  center_sq := center_sq3095
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3095.1
  jac_ok := checks3095.2.1
  accepted := checks3095.2.2

def cells : List CellCertificate := [cell3088, cell3089, cell3090, cell3091, cell3092, cell3093, cell3094, cell3095]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386
