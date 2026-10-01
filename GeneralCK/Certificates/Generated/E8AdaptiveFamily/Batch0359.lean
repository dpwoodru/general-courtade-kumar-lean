import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2872 : RatBall :=
  ⟨⟨-3/640, -51/128⟩, 3/1280⟩
def center2872 : GaussianRat :=
  ⟨-3889311/1000000000, -293038261/1000000000⟩
def contact2872 : RatBall := localContactBall tau2872 center2872
def work2872 : RoundedTauEval :=
  evalTau precision tau2872 contact2872 logTwoBall

theorem center_sq2872 : (center2872.re : ℝ)^2 +
    (center2872.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2872]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2872 : work2872.theta.ok = true ∧
    work2872.jac.invOK = true ∧ acceptsUnitSq work2872.out = true := by
  norm_num [work2872, contact2872, tau2872, center2872, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2872 : CellCertificate where
  tauBall := tau2872
  contactCenter := center2872
  contactBall := contact2872
  work := work2872
  center_sq := center_sq2872
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2872.1
  jac_ok := checks2872.2.1
  accepted := checks2872.2.2

def tau2873 : RatBall :=
  ⟨⟨-1/640, -51/128⟩, 3/1280⟩
def center2873 : GaussianRat :=
  ⟨-162057/125000000, -58609251/200000000⟩
def contact2873 : RatBall := localContactBall tau2873 center2873
def work2873 : RoundedTauEval :=
  evalTau precision tau2873 contact2873 logTwoBall

theorem center_sq2873 : (center2873.re : ℝ)^2 +
    (center2873.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2873]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2873 : work2873.theta.ok = true ∧
    work2873.jac.invOK = true ∧ acceptsUnitSq work2873.out = true := by
  norm_num [work2873, contact2873, tau2873, center2873, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2873 : CellCertificate where
  tauBall := tau2873
  contactCenter := center2873
  contactBall := contact2873
  work := work2873
  center_sq := center_sq2873
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2873.1
  jac_ok := checks2873.2.1
  accepted := checks2873.2.2

def tau2874 : RatBall :=
  ⟨⟨-3/640, -253/640⟩, 3/1280⟩
def center2874 : GaussianRat :=
  ⟨-3877403/1000000000, -36306181/125000000⟩
def contact2874 : RatBall := localContactBall tau2874 center2874
def work2874 : RoundedTauEval :=
  evalTau precision tau2874 contact2874 logTwoBall

theorem center_sq2874 : (center2874.re : ℝ)^2 +
    (center2874.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2874]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2874 : work2874.theta.ok = true ∧
    work2874.jac.invOK = true ∧ acceptsUnitSq work2874.out = true := by
  norm_num [work2874, contact2874, tau2874, center2874, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2874 : CellCertificate where
  tauBall := tau2874
  contactCenter := center2874
  contactBall := contact2874
  work := work2874
  center_sq := center_sq2874
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2874.1
  jac_ok := checks2874.2.1
  accepted := checks2874.2.2

def tau2875 : RatBall :=
  ⟨⟨-1/640, -253/640⟩, 3/1280⟩
def center2875 : GaussianRat :=
  ⟨-646243/500000000, -72614333/250000000⟩
def contact2875 : RatBall := localContactBall tau2875 center2875
def work2875 : RoundedTauEval :=
  evalTau precision tau2875 contact2875 logTwoBall

theorem center_sq2875 : (center2875.re : ℝ)^2 +
    (center2875.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2875]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2875 : work2875.theta.ok = true ∧
    work2875.jac.invOK = true ∧ acceptsUnitSq work2875.out = true := by
  norm_num [work2875, contact2875, tau2875, center2875, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2875 : CellCertificate where
  tauBall := tau2875
  contactCenter := center2875
  contactBall := contact2875
  work := work2875
  center_sq := center_sq2875
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2875.1
  jac_ok := checks2875.2.1
  accepted := checks2875.2.2

def tau2876 : RatBall :=
  ⟨⟨-7/640, -251/640⟩, 3/1280⟩
def center2876 : GaussianRat :=
  ⟨-9019241/1000000000, -287829653/1000000000⟩
def contact2876 : RatBall := localContactBall tau2876 center2876
def work2876 : RoundedTauEval :=
  evalTau precision tau2876 contact2876 logTwoBall

theorem center_sq2876 : (center2876.re : ℝ)^2 +
    (center2876.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2876]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2876 : work2876.theta.ok = true ∧
    work2876.jac.invOK = true ∧ acceptsUnitSq work2876.out = true := by
  norm_num [work2876, contact2876, tau2876, center2876, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2876 : CellCertificate where
  tauBall := tau2876
  contactCenter := center2876
  contactBall := contact2876
  work := work2876
  center_sq := center_sq2876
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2876.1
  jac_ok := checks2876.2.1
  accepted := checks2876.2.2

def tau2877 : RatBall :=
  ⟨⟨-1/128, -251/640⟩, 3/1280⟩
def center2877 : GaussianRat :=
  ⟨-3221293/500000000, -287852971/1000000000⟩
def contact2877 : RatBall := localContactBall tau2877 center2877
def work2877 : RoundedTauEval :=
  evalTau precision tau2877 contact2877 logTwoBall

theorem center_sq2877 : (center2877.re : ℝ)^2 +
    (center2877.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2877]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2877 : work2877.theta.ok = true ∧
    work2877.jac.invOK = true ∧ acceptsUnitSq work2877.out = true := by
  norm_num [work2877, contact2877, tau2877, center2877, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2877 : CellCertificate where
  tauBall := tau2877
  contactCenter := center2877
  contactBall := contact2877
  work := work2877
  center_sq := center_sq2877
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2877.1
  jac_ok := checks2877.2.1
  accepted := checks2877.2.2

def tau2878 : RatBall :=
  ⟨⟨-7/640, -249/640⟩, 3/1280⟩
def center2878 : GaussianRat :=
  ⟨-2248057/250000000, -142628517/500000000⟩
def contact2878 : RatBall := localContactBall tau2878 center2878
def work2878 : RoundedTauEval :=
  evalTau precision tau2878 contact2878 logTwoBall

theorem center_sq2878 : (center2878.re : ℝ)^2 +
    (center2878.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2878]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2878 : work2878.theta.ok = true ∧
    work2878.jac.invOK = true ∧ acceptsUnitSq work2878.out = true := by
  norm_num [work2878, contact2878, tau2878, center2878, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2878 : CellCertificate where
  tauBall := tau2878
  contactCenter := center2878
  contactBall := contact2878
  work := work2878
  center_sq := center_sq2878
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2878.1
  jac_ok := checks2878.2.1
  accepted := checks2878.2.2

def tau2879 : RatBall :=
  ⟨⟨-1/128, -249/640⟩, 3/1280⟩
def center2879 : GaussianRat :=
  ⟨-6423287/1000000000, -285280029/1000000000⟩
def contact2879 : RatBall := localContactBall tau2879 center2879
def work2879 : RoundedTauEval :=
  evalTau precision tau2879 contact2879 logTwoBall

theorem center_sq2879 : (center2879.re : ℝ)^2 +
    (center2879.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2879]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2879 : work2879.theta.ok = true ∧
    work2879.jac.invOK = true ∧ acceptsUnitSq work2879.out = true := by
  norm_num [work2879, contact2879, tau2879, center2879, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2879 : CellCertificate where
  tauBall := tau2879
  contactCenter := center2879
  contactBall := contact2879
  work := work2879
  center_sq := center_sq2879
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2879.1
  jac_ok := checks2879.2.1
  accepted := checks2879.2.2

def cells : List CellCertificate := [cell2872, cell2873, cell2874, cell2875, cell2876, cell2877, cell2878, cell2879]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359
