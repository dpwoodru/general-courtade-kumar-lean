import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0475

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3800 : RatBall :=
  ⟨⟨111/640, 231/640⟩, 3/1280⟩
def center3800 : GaussianRat :=
  ⟨34104423/250000000, 25252199/100000000⟩
def contact3800 : RatBall := localContactBall tau3800 center3800
def work3800 : RoundedTauEval :=
  evalTau precision tau3800 contact3800 logTwoBall

theorem center_sq3800 : (center3800.re : ℝ)^2 +
    (center3800.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3800]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3800 : work3800.theta.ok = true ∧
    work3800.jac.invOK = true ∧ acceptsUnitSq work3800.out = true := by
  norm_num [work3800, contact3800, tau3800, center3800, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3800 : CellCertificate where
  tauBall := tau3800
  contactCenter := center3800
  contactBall := contact3800
  work := work3800
  center_sq := center_sq3800
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3800.1
  jac_ok := checks3800.2.1
  accepted := checks3800.2.2

def tau3801 : RatBall :=
  ⟨⟨97/640, 233/640⟩, 3/1280⟩
def center3801 : GaussianRat :=
  ⟨60018733/500000000, 257196731/1000000000⟩
def contact3801 : RatBall := localContactBall tau3801 center3801
def work3801 : RoundedTauEval :=
  evalTau precision tau3801 contact3801 logTwoBall

theorem center_sq3801 : (center3801.re : ℝ)^2 +
    (center3801.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3801]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3801 : work3801.theta.ok = true ∧
    work3801.jac.invOK = true ∧ acceptsUnitSq work3801.out = true := by
  norm_num [work3801, contact3801, tau3801, center3801, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3801 : CellCertificate where
  tauBall := tau3801
  contactCenter := center3801
  contactBall := contact3801
  work := work3801
  center_sq := center_sq3801
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3801.1
  jac_ok := checks3801.2.1
  accepted := checks3801.2.2

def tau3802 : RatBall :=
  ⟨⟨99/640, 233/640⟩, 3/1280⟩
def center3802 : GaussianRat :=
  ⟨122439891/1000000000, 51376761/200000000⟩
def contact3802 : RatBall := localContactBall tau3802 center3802
def work3802 : RoundedTauEval :=
  evalTau precision tau3802 contact3802 logTwoBall

theorem center_sq3802 : (center3802.re : ℝ)^2 +
    (center3802.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3802]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3802 : work3802.theta.ok = true ∧
    work3802.jac.invOK = true ∧ acceptsUnitSq work3802.out = true := by
  norm_num [work3802, contact3802, tau3802, center3802, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3802 : CellCertificate where
  tauBall := tau3802
  contactCenter := center3802
  contactBall := contact3802
  work := work3802
  center_sq := center_sq3802
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3802.1
  jac_ok := checks3802.2.1
  accepted := checks3802.2.2

def tau3803 : RatBall :=
  ⟨⟨97/640, 47/128⟩, 3/1280⟩
def center3803 : GaussianRat :=
  ⟨15043717/125000000, 259604029/1000000000⟩
def contact3803 : RatBall := localContactBall tau3803 center3803
def work3803 : RoundedTauEval :=
  evalTau precision tau3803 contact3803 logTwoBall

theorem center_sq3803 : (center3803.re : ℝ)^2 +
    (center3803.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3803]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3803 : work3803.theta.ok = true ∧
    work3803.jac.invOK = true ∧ acceptsUnitSq work3803.out = true := by
  norm_num [work3803, contact3803, tau3803, center3803, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3803 : CellCertificate where
  tauBall := tau3803
  contactCenter := center3803
  contactBall := contact3803
  work := work3803
  center_sq := center_sq3803
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3803.1
  jac_ok := checks3803.2.1
  accepted := checks3803.2.2

def tau3804 : RatBall :=
  ⟨⟨99/640, 47/128⟩, 3/1280⟩
def center3804 : GaussianRat :=
  ⟨61378847/500000000, 129643433/500000000⟩
def contact3804 : RatBall := localContactBall tau3804 center3804
def work3804 : RoundedTauEval :=
  evalTau precision tau3804 contact3804 logTwoBall

theorem center_sq3804 : (center3804.re : ℝ)^2 +
    (center3804.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3804]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3804 : work3804.theta.ok = true ∧
    work3804.jac.invOK = true ∧ acceptsUnitSq work3804.out = true := by
  norm_num [work3804, contact3804, tau3804, center3804, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3804 : CellCertificate where
  tauBall := tau3804
  contactCenter := center3804
  contactBall := contact3804
  work := work3804
  center_sq := center_sq3804
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3804.1
  jac_ok := checks3804.2.1
  accepted := checks3804.2.2

def tau3805 : RatBall :=
  ⟨⟨101/640, 233/640⟩, 3/1280⟩
def center3805 : GaussianRat :=
  ⟨124838069/1000000000, 64141351/250000000⟩
def contact3805 : RatBall := localContactBall tau3805 center3805
def work3805 : RoundedTauEval :=
  evalTau precision tau3805 contact3805 logTwoBall

theorem center_sq3805 : (center3805.re : ℝ)^2 +
    (center3805.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3805]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3805 : work3805.theta.ok = true ∧
    work3805.jac.invOK = true ∧ acceptsUnitSq work3805.out = true := by
  norm_num [work3805, contact3805, tau3805, center3805, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3805 : CellCertificate where
  tauBall := tau3805
  contactCenter := center3805
  contactBall := contact3805
  work := work3805
  center_sq := center_sq3805
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3805.1
  jac_ok := checks3805.2.1
  accepted := checks3805.2.2

def tau3806 : RatBall :=
  ⟨⟨103/640, 233/640⟩, 3/1280⟩
def center3806 : GaussianRat :=
  ⟨1987999/15625000, 12812079/50000000⟩
def contact3806 : RatBall := localContactBall tau3806 center3806
def work3806 : RoundedTauEval :=
  evalTau precision tau3806 contact3806 logTwoBall

theorem center_sq3806 : (center3806.re : ℝ)^2 +
    (center3806.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3806]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3806 : work3806.theta.ok = true ∧
    work3806.jac.invOK = true ∧ acceptsUnitSq work3806.out = true := by
  norm_num [work3806, contact3806, tau3806, center3806, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3806 : CellCertificate where
  tauBall := tau3806
  contactCenter := center3806
  contactBall := contact3806
  work := work3806
  center_sq := center_sq3806
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3806.1
  jac_ok := checks3806.2.1
  accepted := checks3806.2.2

def tau3807 : RatBall :=
  ⟨⟨101/640, 47/128⟩, 3/1280⟩
def center3807 : GaussianRat :=
  ⟨25032271/200000000, 809263/3125000⟩
def contact3807 : RatBall := localContactBall tau3807 center3807
def work3807 : RoundedTauEval :=
  evalTau precision tau3807 contact3807 logTwoBall

theorem center_sq3807 : (center3807.re : ℝ)^2 +
    (center3807.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3807]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3807 : work3807.theta.ok = true ∧
    work3807.jac.invOK = true ∧ acceptsUnitSq work3807.out = true := by
  norm_num [work3807, contact3807, tau3807, center3807, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell3807 : CellCertificate where
  tauBall := tau3807
  contactCenter := center3807
  contactBall := contact3807
  work := work3807
  center_sq := center_sq3807
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3807.1
  jac_ok := checks3807.2.1
  accepted := checks3807.2.2

def cells : List CellCertificate := [cell3800, cell3801, cell3802, cell3803, cell3804, cell3805, cell3806, cell3807]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0475
