import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2808 : RatBall :=
  ⟨⟨-31/640, -51/128⟩, 3/1280⟩
def center2808 : GaussianRat :=
  ⟨-20060649/500000000, -146045357/500000000⟩
def contact2808 : RatBall := localContactBall tau2808 center2808
def work2808 : RoundedTauEval :=
  evalTau precision tau2808 contact2808 logTwoBall

theorem center_sq2808 : (center2808.re : ℝ)^2 +
    (center2808.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2808]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2808 : work2808.theta.ok = true ∧
    work2808.jac.invOK = true ∧ acceptsUnitSq work2808.out = true := by
  norm_num [work2808, contact2808, tau2808, center2808, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2808 : CellCertificate where
  tauBall := tau2808
  contactCenter := center2808
  contactBall := contact2808
  work := work2808
  center_sq := center_sq2808
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2808.1
  jac_ok := checks2808.2.1
  accepted := checks2808.2.2

def tau2809 : RatBall :=
  ⟨⟨-29/640, -51/128⟩, 3/1280⟩
def center2809 : GaussianRat :=
  ⟨-2346303/62500000, -292209741/1000000000⟩
def contact2809 : RatBall := localContactBall tau2809 center2809
def work2809 : RoundedTauEval :=
  evalTau precision tau2809 contact2809 logTwoBall

theorem center_sq2809 : (center2809.re : ℝ)^2 +
    (center2809.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2809]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2809 : work2809.theta.ok = true ∧
    work2809.jac.invOK = true ∧ acceptsUnitSq work2809.out = true := by
  norm_num [work2809, contact2809, tau2809, center2809, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2809 : CellCertificate where
  tauBall := tau2809
  contactCenter := center2809
  contactBall := contact2809
  work := work2809
  center_sq := center_sq2809
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2809.1
  jac_ok := checks2809.2.1
  accepted := checks2809.2.2

def tau2810 : RatBall :=
  ⟨⟨-31/640, -253/640⟩, 3/1280⟩
def center2810 : GaussianRat :=
  ⟨-9999803/250000000, -36189373/125000000⟩
def contact2810 : RatBall := localContactBall tau2810 center2810
def work2810 : RoundedTauEval :=
  evalTau precision tau2810 contact2810 logTwoBall

theorem center_sq2810 : (center2810.re : ℝ)^2 +
    (center2810.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2810]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2810 : work2810.theta.ok = true ∧
    work2810.jac.invOK = true ∧ acceptsUnitSq work2810.out = true := by
  norm_num [work2810, contact2810, tau2810, center2810, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2810 : CellCertificate where
  tauBall := tau2810
  contactCenter := center2810
  contactBall := contact2810
  work := work2810
  center_sq := center_sq2810
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2810.1
  jac_ok := checks2810.2.1
  accepted := checks2810.2.2

def tau2811 : RatBall :=
  ⟨⟨-29/640, -253/640⟩, 3/1280⟩
def center2811 : GaussianRat :=
  ⟨-18713263/500000000, -289632371/1000000000⟩
def contact2811 : RatBall := localContactBall tau2811 center2811
def work2811 : RoundedTauEval :=
  evalTau precision tau2811 contact2811 logTwoBall

theorem center_sq2811 : (center2811.re : ℝ)^2 +
    (center2811.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2811]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2811 : work2811.theta.ok = true ∧
    work2811.jac.invOK = true ∧ acceptsUnitSq work2811.out = true := by
  norm_num [work2811, contact2811, tau2811, center2811, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2811 : CellCertificate where
  tauBall := tau2811
  contactCenter := center2811
  contactBall := contact2811
  work := work2811
  center_sq := center_sq2811
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2811.1
  jac_ok := checks2811.2.1
  accepted := checks2811.2.2

def tau2812 : RatBall :=
  ⟨⟨-27/640, -51/128⟩, 3/1280⟩
def center2812 : GaussianRat :=
  ⟨-34958801/1000000000, -14616047/50000000⟩
def contact2812 : RatBall := localContactBall tau2812 center2812
def work2812 : RoundedTauEval :=
  evalTau precision tau2812 contact2812 logTwoBall

theorem center_sq2812 : (center2812.re : ℝ)^2 +
    (center2812.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2812]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2812 : work2812.theta.ok = true ∧
    work2812.jac.invOK = true ∧ acceptsUnitSq work2812.out = true := by
  norm_num [work2812, contact2812, tau2812, center2812, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2812 : CellCertificate where
  tauBall := tau2812
  contactCenter := center2812
  contactBall := contact2812
  work := work2812
  center_sq := center_sq2812
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2812.1
  jac_ok := checks2812.2.1
  accepted := checks2812.2.2

def tau2813 : RatBall :=
  ⟨⟨-5/128, -51/128⟩, 3/1280⟩
def center2813 : GaussianRat :=
  ⟨-32375263/1000000000, -292424289/1000000000⟩
def contact2813 : RatBall := localContactBall tau2813 center2813
def work2813 : RoundedTauEval :=
  evalTau precision tau2813 contact2813 logTwoBall

theorem center_sq2813 : (center2813.re : ℝ)^2 +
    (center2813.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2813]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2813 : work2813.theta.ok = true ∧
    work2813.jac.invOK = true ∧ acceptsUnitSq work2813.out = true := by
  norm_num [work2813, contact2813, tau2813, center2813, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2813 : CellCertificate where
  tauBall := tau2813
  contactCenter := center2813
  contactBall := contact2813
  work := work2813
  center_sq := center_sq2813
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2813.1
  jac_ok := checks2813.2.1
  accepted := checks2813.2.2

def tau2814 : RatBall :=
  ⟨⟨-27/640, -253/640⟩, 3/1280⟩
def center2814 : GaussianRat :=
  ⟨-6970453/200000000, -289742037/1000000000⟩
def contact2814 : RatBall := localContactBall tau2814 center2814
def work2814 : RoundedTauEval :=
  evalTau precision tau2814 contact2814 logTwoBall

theorem center_sq2814 : (center2814.re : ℝ)^2 +
    (center2814.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2814]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2814 : work2814.theta.ok = true ∧
    work2814.jac.invOK = true ∧ acceptsUnitSq work2814.out = true := by
  norm_num [work2814, contact2814, tau2814, center2814, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2814 : CellCertificate where
  tauBall := tau2814
  contactCenter := center2814
  contactBall := contact2814
  work := work2814
  center_sq := center_sq2814
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2814.1
  jac_ok := checks2814.2.1
  accepted := checks2814.2.2

def tau2815 : RatBall :=
  ⟨⟨-5/128, -253/640⟩, 3/1280⟩
def center2815 : GaussianRat :=
  ⟨-16138267/500000000, -7246099/25000000⟩
def contact2815 : RatBall := localContactBall tau2815 center2815
def work2815 : RoundedTauEval :=
  evalTau precision tau2815 contact2815 logTwoBall

theorem center_sq2815 : (center2815.re : ℝ)^2 +
    (center2815.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2815]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2815 : work2815.theta.ok = true ∧
    work2815.jac.invOK = true ∧ acceptsUnitSq work2815.out = true := by
  norm_num [work2815, contact2815, tau2815, center2815, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2815 : CellCertificate where
  tauBall := tau2815
  contactCenter := center2815
  contactBall := contact2815
  work := work2815
  center_sq := center_sq2815
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2815.1
  jac_ok := checks2815.2.1
  accepted := checks2815.2.2

def cells : List CellCertificate := [cell2808, cell2809, cell2810, cell2811, cell2812, cell2813, cell2814, cell2815]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351
