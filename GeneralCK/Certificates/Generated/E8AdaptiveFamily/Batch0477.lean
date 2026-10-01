import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3816 : RatBall :=
  ⟨⟨113/640, 227/640⟩, 3/1280⟩
def center3816 : GaussianRat :=
  ⟨138097011/1000000000, 61864659/250000000⟩
def contact3816 : RatBall := localContactBall tau3816 center3816
def work3816 : RoundedTauEval :=
  evalTau precision tau3816 contact3816 logTwoBall

theorem center_sq3816 : (center3816.re : ℝ)^2 +
    (center3816.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3816]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3816 : work3816.theta.ok = true ∧
    work3816.jac.invOK = true ∧ acceptsUnitSq work3816.out = true := by
  norm_num [work3816, contact3816, tau3816, center3816, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3816 : CellCertificate where
  tauBall := tau3816
  contactCenter := center3816
  contactBall := contact3816
  work := work3816
  center_sq := center_sq3816
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3816.1
  jac_ok := checks3816.2.1
  accepted := checks3816.2.2

def tau3817 : RatBall :=
  ⟨⟨23/128, 227/640⟩, 3/1280⟩
def center3817 : GaussianRat :=
  ⟨140448677/1000000000, 247117293/1000000000⟩
def contact3817 : RatBall := localContactBall tau3817 center3817
def work3817 : RoundedTauEval :=
  evalTau precision tau3817 contact3817 logTwoBall

theorem center_sq3817 : (center3817.re : ℝ)^2 +
    (center3817.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3817]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3817 : work3817.theta.ok = true ∧
    work3817.jac.invOK = true ∧ acceptsUnitSq work3817.out = true := by
  norm_num [work3817, contact3817, tau3817, center3817, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3817 : CellCertificate where
  tauBall := tau3817
  contactCenter := center3817
  contactBall := contact3817
  work := work3817
  center_sq := center_sq3817
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3817.1
  jac_ok := checks3817.2.1
  accepted := checks3817.2.2

def tau3818 : RatBall :=
  ⟨⟨117/640, 45/128⟩, 3/1280⟩
def center3818 : GaussianRat :=
  ⟨8903089/62500000, 244428717/1000000000⟩
def contact3818 : RatBall := localContactBall tau3818 center3818
def work3818 : RoundedTauEval :=
  evalTau precision tau3818 contact3818 logTwoBall

theorem center_sq3818 : (center3818.re : ℝ)^2 +
    (center3818.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3818]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3818 : work3818.theta.ok = true ∧
    work3818.jac.invOK = true ∧ acceptsUnitSq work3818.out = true := by
  norm_num [work3818, contact3818, tau3818, center3818, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3818 : CellCertificate where
  tauBall := tau3818
  contactCenter := center3818
  contactBall := contact3818
  work := work3818
  center_sq := center_sq3818
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3818.1
  jac_ok := checks3818.2.1
  accepted := checks3818.2.2

def tau3819 : RatBall :=
  ⟨⟨119/640, 45/128⟩, 3/1280⟩
def center3819 : GaussianRat :=
  ⟨72393537/500000000, 122041161/500000000⟩
def contact3819 : RatBall := localContactBall tau3819 center3819
def work3819 : RoundedTauEval :=
  evalTau precision tau3819 contact3819 logTwoBall

theorem center_sq3819 : (center3819.re : ℝ)^2 +
    (center3819.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3819]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3819 : work3819.theta.ok = true ∧
    work3819.jac.invOK = true ∧ acceptsUnitSq work3819.out = true := by
  norm_num [work3819, contact3819, tau3819, center3819, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3819 : CellCertificate where
  tauBall := tau3819
  contactCenter := center3819
  contactBall := contact3819
  work := work3819
  center_sq := center_sq3819
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3819.1
  jac_ok := checks3819.2.1
  accepted := checks3819.2.2

def tau3820 : RatBall :=
  ⟨⟨117/640, 227/640⟩, 3/1280⟩
def center3820 : GaussianRat :=
  ⟨142795751/1000000000, 246771071/1000000000⟩
def contact3820 : RatBall := localContactBall tau3820 center3820
def work3820 : RoundedTauEval :=
  evalTau precision tau3820 contact3820 logTwoBall

theorem center_sq3820 : (center3820.re : ℝ)^2 +
    (center3820.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3820]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3820 : work3820.theta.ok = true ∧
    work3820.jac.invOK = true ∧ acceptsUnitSq work3820.out = true := by
  norm_num [work3820, contact3820, tau3820, center3820, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3820 : CellCertificate where
  tauBall := tau3820
  contactCenter := center3820
  contactBall := contact3820
  work := work3820
  center_sq := center_sq3820
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3820.1
  jac_ok := checks3820.2.1
  accepted := checks3820.2.2

def tau3821 : RatBall :=
  ⟨⟨119/640, 227/640⟩, 3/1280⟩
def center3821 : GaussianRat :=
  ⟨145138173/1000000000, 123210011/500000000⟩
def contact3821 : RatBall := localContactBall tau3821 center3821
def work3821 : RoundedTauEval :=
  evalTau precision tau3821 contact3821 logTwoBall

theorem center_sq3821 : (center3821.re : ℝ)^2 +
    (center3821.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3821]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3821 : work3821.theta.ok = true ∧
    work3821.jac.invOK = true ∧ acceptsUnitSq work3821.out = true := by
  norm_num [work3821, contact3821, tau3821, center3821, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3821 : CellCertificate where
  tauBall := tau3821
  contactCenter := center3821
  contactBall := contact3821
  work := work3821
  center_sq := center_sq3821
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3821.1
  jac_ok := checks3821.2.1
  accepted := checks3821.2.2

def tau3822 : RatBall :=
  ⟨⟨113/640, 229/640⟩, 3/1280⟩
def center3822 : GaussianRat :=
  ⟨69219087/500000000, 49963011/200000000⟩
def contact3822 : RatBall := localContactBall tau3822 center3822
def work3822 : RoundedTauEval :=
  evalTau precision tau3822 contact3822 logTwoBall

theorem center_sq3822 : (center3822.re : ℝ)^2 +
    (center3822.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3822]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3822 : work3822.theta.ok = true ∧
    work3822.jac.invOK = true ∧ acceptsUnitSq work3822.out = true := by
  norm_num [work3822, contact3822, tau3822, center3822, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3822 : CellCertificate where
  tauBall := tau3822
  contactCenter := center3822
  contactBall := contact3822
  work := work3822
  center_sq := center_sq3822
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3822.1
  jac_ok := checks3822.2.1
  accepted := checks3822.2.2

def tau3823 : RatBall :=
  ⟨⟨23/128, 229/640⟩, 3/1280⟩
def center3823 : GaussianRat :=
  ⟨70397387/500000000, 249469121/1000000000⟩
def contact3823 : RatBall := localContactBall tau3823 center3823
def work3823 : RoundedTauEval :=
  evalTau precision tau3823 contact3823 logTwoBall

theorem center_sq3823 : (center3823.re : ℝ)^2 +
    (center3823.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3823]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3823 : work3823.theta.ok = true ∧
    work3823.jac.invOK = true ∧ acceptsUnitSq work3823.out = true := by
  norm_num [work3823, contact3823, tau3823, center3823, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3823 : CellCertificate where
  tauBall := tau3823
  contactCenter := center3823
  contactBall := contact3823
  work := work3823
  center_sq := center_sq3823
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3823.1
  jac_ok := checks3823.2.1
  accepted := checks3823.2.2

def cells : List CellCertificate := [cell3816, cell3817, cell3818, cell3819, cell3820, cell3821, cell3822, cell3823]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477
