import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2728 : RatBall :=
  ⟨⟨-53/640, -249/640⟩, 3/1280⟩
def center2728 : GaussianRat :=
  ⟨-33881037/500000000, -282642041/1000000000⟩
def contact2728 : RatBall := localContactBall tau2728 center2728
def work2728 : RoundedTauEval :=
  evalTau precision tau2728 contact2728 logTwoBall

theorem center_sq2728 : (center2728.re : ℝ)^2 +
    (center2728.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2728]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2728 : work2728.theta.ok = true ∧
    work2728.jac.invOK = true ∧ acceptsUnitSq work2728.out = true := by
  norm_num [work2728, contact2728, tau2728, center2728, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2728 : CellCertificate where
  tauBall := tau2728
  contactCenter := center2728
  contactBall := contact2728
  work := work2728
  center_sq := center_sq2728
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2728.1
  jac_ok := checks2728.2.1
  accepted := checks2728.2.2

def tau2729 : RatBall :=
  ⟨⟨-51/640, -251/640⟩, 3/1280⟩
def center2729 : GaussianRat :=
  ⟨-65420927/1000000000, -285375989/1000000000⟩
def contact2729 : RatBall := localContactBall tau2729 center2729
def work2729 : RoundedTauEval :=
  evalTau precision tau2729 contact2729 logTwoBall

theorem center_sq2729 : (center2729.re : ℝ)^2 +
    (center2729.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2729]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2729 : work2729.theta.ok = true ∧
    work2729.jac.invOK = true ∧ acceptsUnitSq work2729.out = true := by
  norm_num [work2729, contact2729, tau2729, center2729, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2729 : CellCertificate where
  tauBall := tau2729
  contactCenter := center2729
  contactBall := contact2729
  work := work2729
  center_sq := center_sq2729
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2729.1
  jac_ok := checks2729.2.1
  accepted := checks2729.2.2

def tau2730 : RatBall :=
  ⟨⟨-49/640, -251/640⟩, 3/1280⟩
def center2730 : GaussianRat :=
  ⟨-6287709/100000000, -142783229/500000000⟩
def contact2730 : RatBall := localContactBall tau2730 center2730
def work2730 : RoundedTauEval :=
  evalTau precision tau2730 contact2730 logTwoBall

theorem center_sq2730 : (center2730.re : ℝ)^2 +
    (center2730.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2730]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2730 : work2730.theta.ok = true ∧
    work2730.jac.invOK = true ∧ acceptsUnitSq work2730.out = true := by
  norm_num [work2730, contact2730, tau2730, center2730, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2730 : CellCertificate where
  tauBall := tau2730
  contactCenter := center2730
  contactBall := contact2730
  work := work2730
  center_sq := center_sq2730
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2730.1
  jac_ok := checks2730.2.1
  accepted := checks2730.2.2

def tau2731 : RatBall :=
  ⟨⟨-51/640, -249/640⟩, 3/1280⟩
def center2731 : GaussianRat :=
  ⟨-13045627/200000000, -141418551/500000000⟩
def contact2731 : RatBall := localContactBall tau2731 center2731
def work2731 : RoundedTauEval :=
  evalTau precision tau2731 contact2731 logTwoBall

theorem center_sq2731 : (center2731.re : ℝ)^2 +
    (center2731.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2731]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2731 : work2731.theta.ok = true ∧
    work2731.jac.invOK = true ∧ acceptsUnitSq work2731.out = true := by
  norm_num [work2731, contact2731, tau2731, center2731, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2731 : CellCertificate where
  tauBall := tau2731
  contactCenter := center2731
  contactBall := contact2731
  work := work2731
  center_sq := center_sq2731
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2731.1
  jac_ok := checks2731.2.1
  accepted := checks2731.2.2

def tau2732 : RatBall :=
  ⟨⟨-49/640, -249/640⟩, 3/1280⟩
def center2732 : GaussianRat :=
  ⟨-62691561/1000000000, -141512483/500000000⟩
def contact2732 : RatBall := localContactBall tau2732 center2732
def work2732 : RoundedTauEval :=
  evalTau precision tau2732 contact2732 logTwoBall

theorem center_sq2732 : (center2732.re : ℝ)^2 +
    (center2732.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2732]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2732 : work2732.theta.ok = true ∧
    work2732.jac.invOK = true ∧ acceptsUnitSq work2732.out = true := by
  norm_num [work2732, contact2732, tau2732, center2732, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2732 : CellCertificate where
  tauBall := tau2732
  contactCenter := center2732
  contactBall := contact2732
  work := work2732
  center_sq := center_sq2732
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2732.1
  jac_ok := checks2732.2.1
  accepted := checks2732.2.2

def tau2733 : RatBall :=
  ⟨⟨-63/640, -247/640⟩, 3/1280⟩
def center2733 : GaussianRat :=
  ⟨-40078273/500000000, -69761453/250000000⟩
def contact2733 : RatBall := localContactBall tau2733 center2733
def work2733 : RoundedTauEval :=
  evalTau precision tau2733 contact2733 logTwoBall

theorem center_sq2733 : (center2733.re : ℝ)^2 +
    (center2733.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2733]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2733 : work2733.theta.ok = true ∧
    work2733.jac.invOK = true ∧ acceptsUnitSq work2733.out = true := by
  norm_num [work2733, contact2733, tau2733, center2733, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2733 : CellCertificate where
  tauBall := tau2733
  contactCenter := center2733
  contactBall := contact2733
  work := work2733
  center_sq := center_sq2733
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2733.1
  jac_ok := checks2733.2.1
  accepted := checks2733.2.2

def tau2734 : RatBall :=
  ⟨⟨-61/640, -247/640⟩, 3/1280⟩
def center2734 : GaussianRat :=
  ⟨-77644141/1000000000, -139636577/500000000⟩
def contact2734 : RatBall := localContactBall tau2734 center2734
def work2734 : RoundedTauEval :=
  evalTau precision tau2734 contact2734 logTwoBall

theorem center_sq2734 : (center2734.re : ℝ)^2 +
    (center2734.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2734]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2734 : work2734.theta.ok = true ∧
    work2734.jac.invOK = true ∧ acceptsUnitSq work2734.out = true := by
  norm_num [work2734, contact2734, tau2734, center2734, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2734 : CellCertificate where
  tauBall := tau2734
  contactCenter := center2734
  contactBall := contact2734
  work := work2734
  center_sq := center_sq2734
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2734.1
  jac_ok := checks2734.2.1
  accepted := checks2734.2.2

def tau2735 : RatBall :=
  ⟨⟨-63/640, -49/128⟩, 3/1280⟩
def center2735 : GaussianRat :=
  ⟨-39963667/500000000, -276538391/1000000000⟩
def contact2735 : RatBall := localContactBall tau2735 center2735
def work2735 : RoundedTauEval :=
  evalTau precision tau2735 contact2735 logTwoBall

theorem center_sq2735 : (center2735.re : ℝ)^2 +
    (center2735.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2735]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2735 : work2735.theta.ok = true ∧
    work2735.jac.invOK = true ∧ acceptsUnitSq work2735.out = true := by
  norm_num [work2735, contact2735, tau2735, center2735, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2735 : CellCertificate where
  tauBall := tau2735
  contactCenter := center2735
  contactBall := contact2735
  work := work2735
  center_sq := center_sq2735
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2735.1
  jac_ok := checks2735.2.1
  accepted := checks2735.2.2

def cells : List CellCertificate := [cell2728, cell2729, cell2730, cell2731, cell2732, cell2733, cell2734, cell2735]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341
