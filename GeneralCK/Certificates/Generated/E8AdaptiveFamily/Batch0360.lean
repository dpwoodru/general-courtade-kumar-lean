import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2880 : RatBall :=
  ⟨⟨-3/640, -251/640⟩, 3/1280⟩
def center2880 : GaussianRat :=
  ⟨-193283/50000000, -143934259/500000000⟩
def contact2880 : RatBall := localContactBall tau2880 center2880
def work2880 : RoundedTauEval :=
  evalTau precision tau2880 contact2880 logTwoBall

theorem center_sq2880 : (center2880.re : ℝ)^2 +
    (center2880.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2880]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2880 : work2880.theta.ok = true ∧
    work2880.jac.invOK = true ∧ acceptsUnitSq work2880.out = true := by
  norm_num [work2880, contact2880, tau2880, center2880, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2880 : CellCertificate where
  tauBall := tau2880
  contactCenter := center2880
  contactBall := contact2880
  work := work2880
  center_sq := center_sq2880
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2880.1
  jac_ok := checks2880.2.1
  accepted := checks2880.2.2

def tau2881 : RatBall :=
  ⟨⟨-1/640, -251/640⟩, 3/1280⟩
def center2881 : GaussianRat :=
  ⟨-1288571/1000000000, -287876293/1000000000⟩
def contact2881 : RatBall := localContactBall tau2881 center2881
def work2881 : RoundedTauEval :=
  evalTau precision tau2881 contact2881 logTwoBall

theorem center_sq2881 : (center2881.re : ℝ)^2 +
    (center2881.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2881]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2881 : work2881.theta.ok = true ∧
    work2881.jac.invOK = true ∧ acceptsUnitSq work2881.out = true := by
  norm_num [work2881, contact2881, tau2881, center2881, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2881 : CellCertificate where
  tauBall := tau2881
  contactCenter := center2881
  contactBall := contact2881
  work := work2881
  center_sq := center_sq2881
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2881.1
  jac_ok := checks2881.2.1
  accepted := checks2881.2.2

def tau2882 : RatBall :=
  ⟨⟨-3/640, -249/640⟩, 3/1280⟩
def center2882 : GaussianRat :=
  ⟨-3854079/1000000000, -142647681/500000000⟩
def contact2882 : RatBall := localContactBall tau2882 center2882
def work2882 : RoundedTauEval :=
  evalTau precision tau2882 contact2882 logTwoBall

theorem center_sq2882 : (center2882.re : ℝ)^2 +
    (center2882.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2882]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2882 : work2882.theta.ok = true ∧
    work2882.jac.invOK = true ∧ acceptsUnitSq work2882.out = true := by
  norm_num [work2882, contact2882, tau2882, center2882, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2882 : CellCertificate where
  tauBall := tau2882
  contactCenter := center2882
  contactBall := contact2882
  work := work2882
  center_sq := center_sq2882
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2882.1
  jac_ok := checks2882.2.1
  accepted := checks2882.2.2

def tau2883 : RatBall :=
  ⟨⟨-1/640, -249/640⟩, 3/1280⟩
def center2883 : GaussianRat :=
  ⟨-1284711/1000000000, -285303029/1000000000⟩
def contact2883 : RatBall := localContactBall tau2883 center2883
def work2883 : RoundedTauEval :=
  evalTau precision tau2883 contact2883 logTwoBall

theorem center_sq2883 : (center2883.re : ℝ)^2 +
    (center2883.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2883]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2883 : work2883.theta.ok = true ∧
    work2883.jac.invOK = true ∧ acceptsUnitSq work2883.out = true := by
  norm_num [work2883, contact2883, tau2883, center2883, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2883 : CellCertificate where
  tauBall := tau2883
  contactCenter := center2883
  contactBall := contact2883
  work := work2883
  center_sq := center_sq2883
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2883.1
  jac_ok := checks2883.2.1
  accepted := checks2883.2.2

def tau2884 : RatBall :=
  ⟨⟨1/640, -51/128⟩, 3/1280⟩
def center2884 : GaussianRat :=
  ⟨162057/125000000, -58609251/200000000⟩
def contact2884 : RatBall := localContactBall tau2884 center2884
def work2884 : RoundedTauEval :=
  evalTau precision tau2884 contact2884 logTwoBall

theorem center_sq2884 : (center2884.re : ℝ)^2 +
    (center2884.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2884]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2884 : work2884.theta.ok = true ∧
    work2884.jac.invOK = true ∧ acceptsUnitSq work2884.out = true := by
  norm_num [work2884, contact2884, tau2884, center2884, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2884 : CellCertificate where
  tauBall := tau2884
  contactCenter := center2884
  contactBall := contact2884
  work := work2884
  center_sq := center_sq2884
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2884.1
  jac_ok := checks2884.2.1
  accepted := checks2884.2.2

def tau2885 : RatBall :=
  ⟨⟨3/640, -51/128⟩, 3/1280⟩
def center2885 : GaussianRat :=
  ⟨3889311/1000000000, -293038261/1000000000⟩
def contact2885 : RatBall := localContactBall tau2885 center2885
def work2885 : RoundedTauEval :=
  evalTau precision tau2885 contact2885 logTwoBall

theorem center_sq2885 : (center2885.re : ℝ)^2 +
    (center2885.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2885]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2885 : work2885.theta.ok = true ∧
    work2885.jac.invOK = true ∧ acceptsUnitSq work2885.out = true := by
  norm_num [work2885, contact2885, tau2885, center2885, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2885 : CellCertificate where
  tauBall := tau2885
  contactCenter := center2885
  contactBall := contact2885
  work := work2885
  center_sq := center_sq2885
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2885.1
  jac_ok := checks2885.2.1
  accepted := checks2885.2.2

def tau2886 : RatBall :=
  ⟨⟨1/640, -253/640⟩, 3/1280⟩
def center2886 : GaussianRat :=
  ⟨646243/500000000, -72614333/250000000⟩
def contact2886 : RatBall := localContactBall tau2886 center2886
def work2886 : RoundedTauEval :=
  evalTau precision tau2886 contact2886 logTwoBall

theorem center_sq2886 : (center2886.re : ℝ)^2 +
    (center2886.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2886]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2886 : work2886.theta.ok = true ∧
    work2886.jac.invOK = true ∧ acceptsUnitSq work2886.out = true := by
  norm_num [work2886, contact2886, tau2886, center2886, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2886 : CellCertificate where
  tauBall := tau2886
  contactCenter := center2886
  contactBall := contact2886
  work := work2886
  center_sq := center_sq2886
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2886.1
  jac_ok := checks2886.2.1
  accepted := checks2886.2.2

def tau2887 : RatBall :=
  ⟨⟨3/640, -253/640⟩, 3/1280⟩
def center2887 : GaussianRat :=
  ⟨3877403/1000000000, -36306181/125000000⟩
def contact2887 : RatBall := localContactBall tau2887 center2887
def work2887 : RoundedTauEval :=
  evalTau precision tau2887 contact2887 logTwoBall

theorem center_sq2887 : (center2887.re : ℝ)^2 +
    (center2887.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2887]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2887 : work2887.theta.ok = true ∧
    work2887.jac.invOK = true ∧ acceptsUnitSq work2887.out = true := by
  norm_num [work2887, contact2887, tau2887, center2887, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2887 : CellCertificate where
  tauBall := tau2887
  contactCenter := center2887
  contactBall := contact2887
  work := work2887
  center_sq := center_sq2887
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2887.1
  jac_ok := checks2887.2.1
  accepted := checks2887.2.2

def cells : List CellCertificate := [cell2880, cell2881, cell2882, cell2883, cell2884, cell2885, cell2886, cell2887]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360
