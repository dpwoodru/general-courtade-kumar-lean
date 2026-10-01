import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3664 : RatBall :=
  ⟨⟨63/640, 241/640⟩, 3/1280⟩
def center3664 : GaussianRat :=
  ⟨15895643/200000000, 271543799/1000000000⟩
def contact3664 : RatBall := localContactBall tau3664 center3664
def work3664 : RoundedTauEval :=
  evalTau precision tau3664 contact3664 logTwoBall

theorem center_sq3664 : (center3664.re : ℝ)^2 +
    (center3664.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3664]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3664 : work3664.theta.ok = true ∧
    work3664.jac.invOK = true ∧ acceptsUnitSq work3664.out = true := by
  norm_num [work3664, contact3664, tau3664, center3664, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3664 : CellCertificate where
  tauBall := tau3664
  contactCenter := center3664
  contactBall := contact3664
  work := work3664
  center_sq := center_sq3664
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3664.1
  jac_ok := checks3664.2.1
  accepted := checks3664.2.2

def tau3665 : RatBall :=
  ⟨⟨61/640, 243/640⟩, 3/1280⟩
def center3665 : GaussianRat :=
  ⟨77202433/1000000000, 5485179/20000000⟩
def contact3665 : RatBall := localContactBall tau3665 center3665
def work3665 : RoundedTauEval :=
  evalTau precision tau3665 contact3665 logTwoBall

theorem center_sq3665 : (center3665.re : ℝ)^2 +
    (center3665.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3665]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3665 : work3665.theta.ok = true ∧
    work3665.jac.invOK = true ∧ acceptsUnitSq work3665.out = true := by
  norm_num [work3665, contact3665, tau3665, center3665, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3665 : CellCertificate where
  tauBall := tau3665
  contactCenter := center3665
  contactBall := contact3665
  work := work3665
  center_sq := center_sq3665
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3665.1
  jac_ok := checks3665.2.1
  accepted := checks3665.2.2

def tau3666 : RatBall :=
  ⟨⟨63/640, 243/640⟩, 3/1280⟩
def center3666 : GaussianRat :=
  ⟨79701237/1000000000, 274037749/1000000000⟩
def contact3666 : RatBall := localContactBall tau3666 center3666
def work3666 : RoundedTauEval :=
  evalTau precision tau3666 contact3666 logTwoBall

theorem center_sq3666 : (center3666.re : ℝ)^2 +
    (center3666.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3666]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3666 : work3666.theta.ok = true ∧
    work3666.jac.invOK = true ∧ acceptsUnitSq work3666.out = true := by
  norm_num [work3666, contact3666, tau3666, center3666, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3666 : CellCertificate where
  tauBall := tau3666
  contactCenter := center3666
  contactBall := contact3666
  work := work3666
  center_sq := center_sq3666
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3666.1
  jac_ok := checks3666.2.1
  accepted := checks3666.2.2

def tau3667 : RatBall :=
  ⟨⟨57/640, 49/128⟩, 3/1280⟩
def center3667 : GaussianRat :=
  ⟨7240167/100000000, 277190643/1000000000⟩
def contact3667 : RatBall := localContactBall tau3667 center3667
def work3667 : RoundedTauEval :=
  evalTau precision tau3667 contact3667 logTwoBall

theorem center_sq3667 : (center3667.re : ℝ)^2 +
    (center3667.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3667]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3667 : work3667.theta.ok = true ∧
    work3667.jac.invOK = true ∧ acceptsUnitSq work3667.out = true := by
  norm_num [work3667, contact3667, tau3667, center3667, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3667 : CellCertificate where
  tauBall := tau3667
  contactCenter := center3667
  contactBall := contact3667
  work := work3667
  center_sq := center_sq3667
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3667.1
  jac_ok := checks3667.2.1
  accepted := checks3667.2.2

def tau3668 : RatBall :=
  ⟨⟨59/640, 49/128⟩, 3/1280⟩
def center3668 : GaussianRat :=
  ⟨7491319/100000000, 34622509/125000000⟩
def contact3668 : RatBall := localContactBall tau3668 center3668
def work3668 : RoundedTauEval :=
  evalTau precision tau3668 contact3668 logTwoBall

theorem center_sq3668 : (center3668.re : ℝ)^2 +
    (center3668.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3668]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3668 : work3668.theta.ok = true ∧
    work3668.jac.invOK = true ∧ acceptsUnitSq work3668.out = true := by
  norm_num [work3668, contact3668, tau3668, center3668, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3668 : CellCertificate where
  tauBall := tau3668
  contactCenter := center3668
  contactBall := contact3668
  work := work3668
  center_sq := center_sq3668
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3668.1
  jac_ok := checks3668.2.1
  accepted := checks3668.2.2

def tau3669 : RatBall :=
  ⟨⟨57/640, 247/640⟩, 3/1280⟩
def center3669 : GaussianRat :=
  ⟨72610227/1000000000, 34963383/125000000⟩
def contact3669 : RatBall := localContactBall tau3669 center3669
def work3669 : RoundedTauEval :=
  evalTau precision tau3669 contact3669 logTwoBall

theorem center_sq3669 : (center3669.re : ℝ)^2 +
    (center3669.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3669]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3669 : work3669.theta.ok = true ∧
    work3669.jac.invOK = true ∧ acceptsUnitSq work3669.out = true := by
  norm_num [work3669, contact3669, tau3669, center3669, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3669 : CellCertificate where
  tauBall := tau3669
  contactCenter := center3669
  contactBall := contact3669
  work := work3669
  center_sq := center_sq3669
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3669.1
  jac_ok := checks3669.2.1
  accepted := checks3669.2.2

def tau3670 : RatBall :=
  ⟨⟨59/640, 247/640⟩, 3/1280⟩
def center3670 : GaussianRat :=
  ⟨75128671/1000000000, 55898717/200000000⟩
def contact3670 : RatBall := localContactBall tau3670 center3670
def work3670 : RoundedTauEval :=
  evalTau precision tau3670 contact3670 logTwoBall

theorem center_sq3670 : (center3670.re : ℝ)^2 +
    (center3670.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3670]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3670 : work3670.theta.ok = true ∧
    work3670.jac.invOK = true ∧ acceptsUnitSq work3670.out = true := by
  norm_num [work3670, contact3670, tau3670, center3670, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3670 : CellCertificate where
  tauBall := tau3670
  contactCenter := center3670
  contactBall := contact3670
  work := work3670
  center_sq := center_sq3670
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3670.1
  jac_ok := checks3670.2.1
  accepted := checks3670.2.2

def tau3671 : RatBall :=
  ⟨⟨61/640, 49/128⟩, 3/1280⟩
def center3671 : GaussianRat :=
  ⟨3096871/40000000, 138381321/500000000⟩
def contact3671 : RatBall := localContactBall tau3671 center3671
def work3671 : RoundedTauEval :=
  evalTau precision tau3671 contact3671 logTwoBall

theorem center_sq3671 : (center3671.re : ℝ)^2 +
    (center3671.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3671]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3671 : work3671.theta.ok = true ∧
    work3671.jac.invOK = true ∧ acceptsUnitSq work3671.out = true := by
  norm_num [work3671, contact3671, tau3671, center3671, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3671 : CellCertificate where
  tauBall := tau3671
  contactCenter := center3671
  contactBall := contact3671
  work := work3671
  center_sq := center_sq3671
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3671.1
  jac_ok := checks3671.2.1
  accepted := checks3671.2.2

def cells : List CellCertificate := [cell3664, cell3665, cell3666, cell3667, cell3668, cell3669, cell3670, cell3671]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458
