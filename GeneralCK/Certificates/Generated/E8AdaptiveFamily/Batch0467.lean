import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3736 : RatBall :=
  ⟨⟨19/128, 233/640⟩, 3/1280⟩
def center3736 : GaussianRat :=
  ⟨7351929/62500000, 128752067/500000000⟩
def contact3736 : RatBall := localContactBall tau3736 center3736
def work3736 : RoundedTauEval :=
  evalTau precision tau3736 contact3736 logTwoBall

theorem center_sq3736 : (center3736.re : ℝ)^2 +
    (center3736.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3736]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3736 : work3736.theta.ok = true ∧
    work3736.jac.invOK = true ∧ acceptsUnitSq work3736.out = true := by
  norm_num [work3736, contact3736, tau3736, center3736, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3736 : CellCertificate where
  tauBall := tau3736
  contactCenter := center3736
  contactBall := contact3736
  work := work3736
  center_sq := center_sq3736
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3736.1
  jac_ok := checks3736.2.1
  accepted := checks3736.2.2

def tau3737 : RatBall :=
  ⟨⟨93/640, 47/128⟩, 3/1280⟩
def center3737 : GaussianRat :=
  ⟨115521207/1000000000, 32527691/125000000⟩
def contact3737 : RatBall := localContactBall tau3737 center3737
def work3737 : RoundedTauEval :=
  evalTau precision tau3737 contact3737 logTwoBall

theorem center_sq3737 : (center3737.re : ℝ)^2 +
    (center3737.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3737]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3737 : work3737.theta.ok = true ∧
    work3737.jac.invOK = true ∧ acceptsUnitSq work3737.out = true := by
  norm_num [work3737, contact3737, tau3737, center3737, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3737 : CellCertificate where
  tauBall := tau3737
  contactCenter := center3737
  contactBall := contact3737
  work := work3737
  center_sq := center_sq3737
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3737.1
  jac_ok := checks3737.2.1
  accepted := checks3737.2.2

def tau3738 : RatBall :=
  ⟨⟨19/128, 47/128⟩, 3/1280⟩
def center3738 : GaussianRat :=
  ⟨117937551/1000000000, 649789/2500000⟩
def contact3738 : RatBall := localContactBall tau3738 center3738
def work3738 : RoundedTauEval :=
  evalTau precision tau3738 contact3738 logTwoBall

theorem center_sq3738 : (center3738.re : ℝ)^2 +
    (center3738.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3738]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3738 : work3738.theta.ok = true ∧
    work3738.jac.invOK = true ∧ acceptsUnitSq work3738.out = true := by
  norm_num [work3738, contact3738, tau3738, center3738, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3738 : CellCertificate where
  tauBall := tau3738
  contactCenter := center3738
  contactBall := contact3738
  work := work3738
  center_sq := center_sq3738
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3738.1
  jac_ok := checks3738.2.1
  accepted := checks3738.2.2

def tau3739 : RatBall :=
  ⟨⟨89/640, 237/640⟩, 3/1280⟩
def center3739 : GaussianRat :=
  ⟨55484957/500000000, 65811399/250000000⟩
def contact3739 : RatBall := localContactBall tau3739 center3739
def work3739 : RoundedTauEval :=
  evalTau precision tau3739 contact3739 logTwoBall

theorem center_sq3739 : (center3739.re : ℝ)^2 +
    (center3739.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3739]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3739 : work3739.theta.ok = true ∧
    work3739.jac.invOK = true ∧ acceptsUnitSq work3739.out = true := by
  norm_num [work3739, contact3739, tau3739, center3739, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3739 : CellCertificate where
  tauBall := tau3739
  contactCenter := center3739
  contactBall := contact3739
  work := work3739
  center_sq := center_sq3739
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3739.1
  jac_ok := checks3739.2.1
  accepted := checks3739.2.2

def tau3740 : RatBall :=
  ⟨⟨91/640, 237/640⟩, 3/1280⟩
def center3740 : GaussianRat :=
  ⟨22680033/200000000, 131473549/500000000⟩
def contact3740 : RatBall := localContactBall tau3740 center3740
def work3740 : RoundedTauEval :=
  evalTau precision tau3740 contact3740 logTwoBall

theorem center_sq3740 : (center3740.re : ℝ)^2 +
    (center3740.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3740]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3740 : work3740.theta.ok = true ∧
    work3740.jac.invOK = true ∧ acceptsUnitSq work3740.out = true := by
  norm_num [work3740, contact3740, tau3740, center3740, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3740 : CellCertificate where
  tauBall := tau3740
  contactCenter := center3740
  contactBall := contact3740
  work := work3740
  center_sq := center_sq3740
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3740.1
  jac_ok := checks3740.2.1
  accepted := checks3740.2.2

def tau3741 : RatBall :=
  ⟨⟨89/640, 239/640⟩, 3/1280⟩
def center3741 : GaussianRat :=
  ⟨111267493/1000000000, 265680799/1000000000⟩
def contact3741 : RatBall := localContactBall tau3741 center3741
def work3741 : RoundedTauEval :=
  evalTau precision tau3741 contact3741 logTwoBall

theorem center_sq3741 : (center3741.re : ℝ)^2 +
    (center3741.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3741]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3741 : work3741.theta.ok = true ∧
    work3741.jac.invOK = true ∧ acceptsUnitSq work3741.out = true := by
  norm_num [work3741, contact3741, tau3741, center3741, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3741 : CellCertificate where
  tauBall := tau3741
  contactCenter := center3741
  contactBall := contact3741
  work := work3741
  center_sq := center_sq3741
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3741.1
  jac_ok := checks3741.2.1
  accepted := checks3741.2.2

def tau3742 : RatBall :=
  ⟨⟨91/640, 239/640⟩, 3/1280⟩
def center3742 : GaussianRat :=
  ⟨113703619/1000000000, 265378247/1000000000⟩
def contact3742 : RatBall := localContactBall tau3742 center3742
def work3742 : RoundedTauEval :=
  evalTau precision tau3742 contact3742 logTwoBall

theorem center_sq3742 : (center3742.re : ℝ)^2 +
    (center3742.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3742]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3742 : work3742.theta.ok = true ∧
    work3742.jac.invOK = true ∧ acceptsUnitSq work3742.out = true := by
  norm_num [work3742, contact3742, tau3742, center3742, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3742 : CellCertificate where
  tauBall := tau3742
  contactCenter := center3742
  contactBall := contact3742
  work := work3742
  center_sq := center_sq3742
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3742.1
  jac_ok := checks3742.2.1
  accepted := checks3742.2.2

def tau3743 : RatBall :=
  ⟨⟨93/640, 237/640⟩, 3/1280⟩
def center3743 : GaussianRat :=
  ⟨115826349/1000000000, 52528557/200000000⟩
def contact3743 : RatBall := localContactBall tau3743 center3743
def work3743 : RoundedTauEval :=
  evalTau precision tau3743 contact3743 logTwoBall

theorem center_sq3743 : (center3743.re : ℝ)^2 +
    (center3743.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3743]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3743 : work3743.theta.ok = true ∧
    work3743.jac.invOK = true ∧ acceptsUnitSq work3743.out = true := by
  norm_num [work3743, contact3743, tau3743, center3743, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3743 : CellCertificate where
  tauBall := tau3743
  contactCenter := center3743
  contactBall := contact3743
  work := work3743
  center_sq := center_sq3743
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3743.1
  jac_ok := checks3743.2.1
  accepted := checks3743.2.2

def cells : List CellCertificate := [cell3736, cell3737, cell3738, cell3739, cell3740, cell3741, cell3742, cell3743]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467
