import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3160 : RatBall :=
  ⟨⟨109/640, -229/640⟩, 3/1280⟩
def center3160 : GaussianRat :=
  ⟨133711273/1000000000, -250491903/1000000000⟩
def contact3160 : RatBall := localContactBall tau3160 center3160
def work3160 : RoundedTauEval :=
  evalTau precision tau3160 contact3160 logTwoBall

theorem center_sq3160 : (center3160.re : ℝ)^2 +
    (center3160.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3160]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3160 : work3160.theta.ok = true ∧
    work3160.jac.invOK = true ∧ acceptsUnitSq work3160.out = true := by
  norm_num [work3160, contact3160, tau3160, center3160, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3160 : CellCertificate where
  tauBall := tau3160
  contactCenter := center3160
  contactBall := contact3160
  work := work3160
  center_sq := center_sq3160
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3160.1
  jac_ok := checks3160.2.1
  accepted := checks3160.2.2

def tau3161 : RatBall :=
  ⟨⟨111/640, -229/640⟩, 3/1280⟩
def center3161 : GaussianRat :=
  ⟨136076987/1000000000, -250155999/1000000000⟩
def contact3161 : RatBall := localContactBall tau3161 center3161
def work3161 : RoundedTauEval :=
  evalTau precision tau3161 contact3161 logTwoBall

theorem center_sq3161 : (center3161.re : ℝ)^2 +
    (center3161.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3161]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3161 : work3161.theta.ok = true ∧
    work3161.jac.invOK = true ∧ acceptsUnitSq work3161.out = true := by
  norm_num [work3161, contact3161, tau3161, center3161, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3161 : CellCertificate where
  tauBall := tau3161
  contactCenter := center3161
  contactBall := contact3161
  work := work3161
  center_sq := center_sq3161
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3161.1
  jac_ok := checks3161.2.1
  accepted := checks3161.2.2

def tau3162 : RatBall :=
  ⟨⟨109/640, -227/640⟩, 3/1280⟩
def center3162 : GaussianRat :=
  ⟨133380131/1000000000, -248126483/1000000000⟩
def contact3162 : RatBall := localContactBall tau3162 center3162
def work3162 : RoundedTauEval :=
  evalTau precision tau3162 contact3162 logTwoBall

theorem center_sq3162 : (center3162.re : ℝ)^2 +
    (center3162.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3162]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3162 : work3162.theta.ok = true ∧
    work3162.jac.invOK = true ∧ acceptsUnitSq work3162.out = true := by
  norm_num [work3162, contact3162, tau3162, center3162, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3162 : CellCertificate where
  tauBall := tau3162
  contactCenter := center3162
  contactBall := contact3162
  work := work3162
  center_sq := center_sq3162
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3162.1
  jac_ok := checks3162.2.1
  accepted := checks3162.2.2

def tau3163 : RatBall :=
  ⟨⟨111/640, -227/640⟩, 3/1280⟩
def center3163 : GaussianRat :=
  ⟨135740809/1000000000, -4955901/20000000⟩
def contact3163 : RatBall := localContactBall tau3163 center3163
def work3163 : RoundedTauEval :=
  evalTau precision tau3163 contact3163 logTwoBall

theorem center_sq3163 : (center3163.re : ℝ)^2 +
    (center3163.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3163]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3163 : work3163.theta.ok = true ∧
    work3163.jac.invOK = true ∧ acceptsUnitSq work3163.out = true := by
  norm_num [work3163, contact3163, tau3163, center3163, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3163 : CellCertificate where
  tauBall := tau3163
  contactCenter := center3163
  contactBall := contact3163
  work := work3163
  center_sq := center_sq3163
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3163.1
  jac_ok := checks3163.2.1
  accepted := checks3163.2.2

def tau3164 : RatBall :=
  ⟨⟨109/640, -45/128⟩, 3/1280⟩
def center3164 : GaussianRat :=
  ⟨26610681/200000000, -245766093/1000000000⟩
def contact3164 : RatBall := localContactBall tau3164 center3164
def work3164 : RoundedTauEval :=
  evalTau precision tau3164 contact3164 logTwoBall

theorem center_sq3164 : (center3164.re : ℝ)^2 +
    (center3164.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3164]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3164 : work3164.theta.ok = true ∧
    work3164.jac.invOK = true ∧ acceptsUnitSq work3164.out = true := by
  norm_num [work3164, contact3164, tau3164, center3164, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3164 : CellCertificate where
  tauBall := tau3164
  contactCenter := center3164
  contactBall := contact3164
  work := work3164
  center_sq := center_sq3164
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3164.1
  jac_ok := checks3164.2.1
  accepted := checks3164.2.2

def tau3165 : RatBall :=
  ⟨⟨111/640, -45/128⟩, 3/1280⟩
def center3165 : GaussianRat :=
  ⟨67704553/500000000, -6135977/25000000⟩
def contact3165 : RatBall := localContactBall tau3165 center3165
def work3165 : RoundedTauEval :=
  evalTau precision tau3165 contact3165 logTwoBall

theorem center_sq3165 : (center3165.re : ℝ)^2 +
    (center3165.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3165]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3165 : work3165.theta.ok = true ∧
    work3165.jac.invOK = true ∧ acceptsUnitSq work3165.out = true := by
  norm_num [work3165, contact3165, tau3165, center3165, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3165 : CellCertificate where
  tauBall := tau3165
  contactCenter := center3165
  contactBall := contact3165
  work := work3165
  center_sq := center_sq3165
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3165.1
  jac_ok := checks3165.2.1
  accepted := checks3165.2.2

def tau3166 : RatBall :=
  ⟨⟨113/640, -231/640⟩, 3/1280⟩
def center3166 : GaussianRat :=
  ⟨138783923/1000000000, -252176463/1000000000⟩
def contact3166 : RatBall := localContactBall tau3166 center3166
def work3166 : RoundedTauEval :=
  evalTau precision tau3166 contact3166 logTwoBall

theorem center_sq3166 : (center3166.re : ℝ)^2 +
    (center3166.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3166]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3166 : work3166.theta.ok = true ∧
    work3166.jac.invOK = true ∧ acceptsUnitSq work3166.out = true := by
  norm_num [work3166, contact3166, tau3166, center3166, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3166 : CellCertificate where
  tauBall := tau3166
  contactCenter := center3166
  contactBall := contact3166
  work := work3166
  center_sq := center_sq3166
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3166.1
  jac_ok := checks3166.2.1
  accepted := checks3166.2.2

def tau3167 : RatBall :=
  ⟨⟨113/640, -229/640⟩, 3/1280⟩
def center3167 : GaussianRat :=
  ⟨69219087/500000000, -49963011/200000000⟩
def contact3167 : RatBall := localContactBall tau3167 center3167
def work3167 : RoundedTauEval :=
  evalTau precision tau3167 contact3167 logTwoBall

theorem center_sq3167 : (center3167.re : ℝ)^2 +
    (center3167.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3167]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3167 : work3167.theta.ok = true ∧
    work3167.jac.invOK = true ∧ acceptsUnitSq work3167.out = true := by
  norm_num [work3167, contact3167, tau3167, center3167, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3167 : CellCertificate where
  tauBall := tau3167
  contactCenter := center3167
  contactBall := contact3167
  work := work3167
  center_sq := center_sq3167
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3167.1
  jac_ok := checks3167.2.1
  accepted := checks3167.2.2

def cells : List CellCertificate := [cell3160, cell3161, cell3162, cell3163, cell3164, cell3165, cell3166, cell3167]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395
