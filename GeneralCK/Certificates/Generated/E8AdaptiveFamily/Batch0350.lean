import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2800 : RatBall :=
  ⟨⟨-39/640, -247/640⟩, 3/1280⟩
def center2800 : GaussianRat :=
  ⟨-49825917/1000000000, -281309513/1000000000⟩
def contact2800 : RatBall := localContactBall tau2800 center2800
def work2800 : RoundedTauEval :=
  evalTau precision tau2800 contact2800 logTwoBall

theorem center_sq2800 : (center2800.re : ℝ)^2 +
    (center2800.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2800]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2800 : work2800.theta.ok = true ∧
    work2800.jac.invOK = true ∧ acceptsUnitSq work2800.out = true := by
  norm_num [work2800, contact2800, tau2800, center2800, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2800 : CellCertificate where
  tauBall := tau2800
  contactCenter := center2800
  contactBall := contact2800
  work := work2800
  center_sq := center_sq2800
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2800.1
  jac_ok := checks2800.2.1
  accepted := checks2800.2.2

def tau2801 : RatBall :=
  ⟨⟨-37/640, -247/640⟩, 3/1280⟩
def center2801 : GaussianRat :=
  ⟨-11820737/250000000, -11258061/40000000⟩
def contact2801 : RatBall := localContactBall tau2801 center2801
def work2801 : RoundedTauEval :=
  evalTau precision tau2801 contact2801 logTwoBall

theorem center_sq2801 : (center2801.re : ℝ)^2 +
    (center2801.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2801]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2801 : work2801.theta.ok = true ∧
    work2801.jac.invOK = true ∧ acceptsUnitSq work2801.out = true := by
  norm_num [work2801, contact2801, tau2801, center2801, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2801 : CellCertificate where
  tauBall := tau2801
  contactCenter := center2801
  contactBall := contact2801
  work := work2801
  center_sq := center_sq2801
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2801.1
  jac_ok := checks2801.2.1
  accepted := checks2801.2.2

def tau2802 : RatBall :=
  ⟨⟨-39/640, -49/128⟩, 3/1280⟩
def center2802 : GaussianRat :=
  ⟨-49681259/1000000000, -139385581/500000000⟩
def contact2802 : RatBall := localContactBall tau2802 center2802
def work2802 : RoundedTauEval :=
  evalTau precision tau2802 contact2802 logTwoBall

theorem center_sq2802 : (center2802.re : ℝ)^2 +
    (center2802.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2802]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2802 : work2802.theta.ok = true ∧
    work2802.jac.invOK = true ∧ acceptsUnitSq work2802.out = true := by
  norm_num [work2802, contact2802, tau2802, center2802, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2802 : CellCertificate where
  tauBall := tau2802
  contactCenter := center2802
  contactBall := contact2802
  work := work2802
  center_sq := center_sq2802
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2802.1
  jac_ok := checks2802.2.1
  accepted := checks2802.2.2

def tau2803 : RatBall :=
  ⟨⟨-37/640, -49/128⟩, 3/1280⟩
def center2803 : GaussianRat :=
  ⟨-23572771/500000000, -278911223/1000000000⟩
def contact2803 : RatBall := localContactBall tau2803 center2803
def work2803 : RoundedTauEval :=
  evalTau precision tau2803 contact2803 logTwoBall

theorem center_sq2803 : (center2803.re : ℝ)^2 +
    (center2803.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2803]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2803 : work2803.theta.ok = true ∧
    work2803.jac.invOK = true ∧ acceptsUnitSq work2803.out = true := by
  norm_num [work2803, contact2803, tau2803, center2803, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2803 : CellCertificate where
  tauBall := tau2803
  contactCenter := center2803
  contactBall := contact2803
  work := work2803
  center_sq := center_sq2803
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2803.1
  jac_ok := checks2803.2.1
  accepted := checks2803.2.2

def tau2804 : RatBall :=
  ⟨⟨-7/128, -247/640⟩, 3/1280⟩
def center2804 : GaussianRat :=
  ⟨-2796129/62500000, -281586221/1000000000⟩
def contact2804 : RatBall := localContactBall tau2804 center2804
def work2804 : RoundedTauEval :=
  evalTau precision tau2804 contact2804 logTwoBall

theorem center_sq2804 : (center2804.re : ℝ)^2 +
    (center2804.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2804]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2804 : work2804.theta.ok = true ∧
    work2804.jac.invOK = true ∧ acceptsUnitSq work2804.out = true := by
  norm_num [work2804, contact2804, tau2804, center2804, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2804 : CellCertificate where
  tauBall := tau2804
  contactCenter := center2804
  contactBall := contact2804
  work := work2804
  center_sq := center_sq2804
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2804.1
  jac_ok := checks2804.2.1
  accepted := checks2804.2.2

def tau2805 : RatBall :=
  ⟨⟨-33/640, -247/640⟩, 3/1280⟩
def center2805 : GaussianRat :=
  ⟨-8438273/200000000, -281713577/1000000000⟩
def contact2805 : RatBall := localContactBall tau2805 center2805
def work2805 : RoundedTauEval :=
  evalTau precision tau2805 contact2805 logTwoBall

theorem center_sq2805 : (center2805.re : ℝ)^2 +
    (center2805.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2805]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2805 : work2805.theta.ok = true ∧
    work2805.jac.invOK = true ∧ acceptsUnitSq work2805.out = true := by
  norm_num [work2805, contact2805, tau2805, center2805, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2805 : CellCertificate where
  tauBall := tau2805
  contactCenter := center2805
  contactBall := contact2805
  work := work2805
  center_sq := center_sq2805
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2805.1
  jac_ok := checks2805.2.1
  accepted := checks2805.2.2

def tau2806 : RatBall :=
  ⟨⟨-7/128, -49/128⟩, 3/1280⟩
def center2806 : GaussianRat :=
  ⟨-44607937/1000000000, -279044067/1000000000⟩
def contact2806 : RatBall := localContactBall tau2806 center2806
def work2806 : RoundedTauEval :=
  evalTau precision tau2806 contact2806 logTwoBall

theorem center_sq2806 : (center2806.re : ℝ)^2 +
    (center2806.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2806]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2806 : work2806.theta.ok = true ∧
    work2806.jac.invOK = true ∧ acceptsUnitSq work2806.out = true := by
  norm_num [work2806, contact2806, tau2806, center2806, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2806 : CellCertificate where
  tauBall := tau2806
  contactCenter := center2806
  contactBall := contact2806
  work := work2806
  center_sq := center_sq2806
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2806.1
  jac_ok := checks2806.2.1
  accepted := checks2806.2.2

def tau2807 : RatBall :=
  ⟨⟨-33/640, -49/128⟩, 3/1280⟩
def center2807 : GaussianRat :=
  ⟨-42068541/1000000000, -27916967/100000000⟩
def contact2807 : RatBall := localContactBall tau2807 center2807
def work2807 : RoundedTauEval :=
  evalTau precision tau2807 contact2807 logTwoBall

theorem center_sq2807 : (center2807.re : ℝ)^2 +
    (center2807.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2807]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2807 : work2807.theta.ok = true ∧
    work2807.jac.invOK = true ∧ acceptsUnitSq work2807.out = true := by
  norm_num [work2807, contact2807, tau2807, center2807, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2807 : CellCertificate where
  tauBall := tau2807
  contactCenter := center2807
  contactBall := contact2807
  work := work2807
  center_sq := center_sq2807
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2807.1
  jac_ok := checks2807.2.1
  accepted := checks2807.2.2

def cells : List CellCertificate := [cell2800, cell2801, cell2802, cell2803, cell2804, cell2805, cell2806, cell2807]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350
