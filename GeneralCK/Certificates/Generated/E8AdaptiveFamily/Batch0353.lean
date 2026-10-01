import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2824 : RatBall :=
  ⟨⟨-23/640, -51/128⟩, 3/1280⟩
def center2824 : GaussianRat :=
  ⟨-5958069/200000000, -292519767/1000000000⟩
def contact2824 : RatBall := localContactBall tau2824 center2824
def work2824 : RoundedTauEval :=
  evalTau precision tau2824 contact2824 logTwoBall

theorem center_sq2824 : (center2824.re : ℝ)^2 +
    (center2824.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2824]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2824 : work2824.theta.ok = true ∧
    work2824.jac.invOK = true ∧ acceptsUnitSq work2824.out = true := by
  norm_num [work2824, contact2824, tau2824, center2824, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2824 : CellCertificate where
  tauBall := tau2824
  contactCenter := center2824
  contactBall := contact2824
  work := work2824
  center_sq := center_sq2824
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2824.1
  jac_ok := checks2824.2.1
  accepted := checks2824.2.2

def tau2825 : RatBall :=
  ⟨⟨-21/640, -51/128⟩, 3/1280⟩
def center2825 : GaussianRat :=
  ⟨-27204153/1000000000, -58521471/200000000⟩
def contact2825 : RatBall := localContactBall tau2825 center2825
def work2825 : RoundedTauEval :=
  evalTau precision tau2825 contact2825 logTwoBall

theorem center_sq2825 : (center2825.re : ℝ)^2 +
    (center2825.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2825]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2825 : work2825.theta.ok = true ∧
    work2825.jac.invOK = true ∧ acceptsUnitSq work2825.out = true := by
  norm_num [work2825, contact2825, tau2825, center2825, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2825 : CellCertificate where
  tauBall := tau2825
  contactCenter := center2825
  contactBall := contact2825
  work := work2825
  center_sq := center_sq2825
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2825.1
  jac_ok := checks2825.2.1
  accepted := checks2825.2.2

def tau2826 : RatBall :=
  ⟨⟨-23/640, -253/640⟩, 3/1280⟩
def center2826 : GaussianRat :=
  ⟨-14849721/500000000, -7248453/25000000⟩
def contact2826 : RatBall := localContactBall tau2826 center2826
def work2826 : RoundedTauEval :=
  evalTau precision tau2826 contact2826 logTwoBall

theorem center_sq2826 : (center2826.re : ℝ)^2 +
    (center2826.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2826]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2826 : work2826.theta.ok = true ∧
    work2826.jac.invOK = true ∧ acceptsUnitSq work2826.out = true := by
  norm_num [work2826, contact2826, tau2826, center2826, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2826 : CellCertificate where
  tauBall := tau2826
  contactCenter := center2826
  contactBall := contact2826
  work := work2826
  center_sq := center_sq2826
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2826.1
  jac_ok := checks2826.2.1
  accepted := checks2826.2.2

def tau2827 : RatBall :=
  ⟨⟨-21/640, -253/640⟩, 3/1280⟩
def center2827 : GaussianRat :=
  ⟨-5424219/200000000, -290024499/1000000000⟩
def contact2827 : RatBall := localContactBall tau2827 center2827
def work2827 : RoundedTauEval :=
  evalTau precision tau2827 contact2827 logTwoBall

theorem center_sq2827 : (center2827.re : ℝ)^2 +
    (center2827.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2827]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2827 : work2827.theta.ok = true ∧
    work2827.jac.invOK = true ∧ acceptsUnitSq work2827.out = true := by
  norm_num [work2827, contact2827, tau2827, center2827, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2827 : CellCertificate where
  tauBall := tau2827
  contactCenter := center2827
  contactBall := contact2827
  work := work2827
  center_sq := center_sq2827
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2827.1
  jac_ok := checks2827.2.1
  accepted := checks2827.2.2

def tau2828 : RatBall :=
  ⟨⟨-19/640, -51/128⟩, 3/1280⟩
def center2828 : GaussianRat :=
  ⟨-24616799/1000000000, -73171759/250000000⟩
def contact2828 : RatBall := localContactBall tau2828 center2828
def work2828 : RoundedTauEval :=
  evalTau precision tau2828 contact2828 logTwoBall

theorem center_sq2828 : (center2828.re : ℝ)^2 +
    (center2828.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2828]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2828 : work2828.theta.ok = true ∧
    work2828.jac.invOK = true ∧ acceptsUnitSq work2828.out = true := by
  norm_num [work2828, contact2828, tau2828, center2828, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2828 : CellCertificate where
  tauBall := tau2828
  contactCenter := center2828
  contactBall := contact2828
  work := work2828
  center_sq := center_sq2828
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2828.1
  jac_ok := checks2828.2.1
  accepted := checks2828.2.2

def tau2829 : RatBall :=
  ⟨⟨-17/640, -51/128⟩, 3/1280⟩
def center2829 : GaussianRat :=
  ⟨-22028391/1000000000, -146379397/500000000⟩
def contact2829 : RatBall := localContactBall tau2829 center2829
def work2829 : RoundedTauEval :=
  evalTau precision tau2829 contact2829 logTwoBall

theorem center_sq2829 : (center2829.re : ℝ)^2 +
    (center2829.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2829]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2829 : work2829.theta.ok = true ∧
    work2829.jac.invOK = true ∧ acceptsUnitSq work2829.out = true := by
  norm_num [work2829, contact2829, tau2829, center2829, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2829 : CellCertificate where
  tauBall := tau2829
  contactCenter := center2829
  contactBall := contact2829
  work := work2829
  center_sq := center_sq2829
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2829.1
  jac_ok := checks2829.2.1
  accepted := checks2829.2.2

def tau2830 : RatBall :=
  ⟨⟨-19/640, -253/640⟩, 3/1280⟩
def center2830 : GaussianRat :=
  ⟨-24541601/1000000000, -290103079/1000000000⟩
def contact2830 : RatBall := localContactBall tau2830 center2830
def work2830 : RoundedTauEval :=
  evalTau precision tau2830 contact2830 logTwoBall

theorem center_sq2830 : (center2830.re : ℝ)^2 +
    (center2830.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2830]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2830 : work2830.theta.ok = true ∧
    work2830.jac.invOK = true ∧ acceptsUnitSq work2830.out = true := by
  norm_num [work2830, contact2830, tau2830, center2830, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2830 : CellCertificate where
  tauBall := tau2830
  contactCenter := center2830
  contactBall := contact2830
  work := work2830
  center_sq := center_sq2830
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2830.1
  jac_ok := checks2830.2.1
  accepted := checks2830.2.2

def tau2831 : RatBall :=
  ⟨⟨-17/640, -253/640⟩, 3/1280⟩
def center2831 : GaussianRat :=
  ⟨-21961069/1000000000, -145086923/500000000⟩
def contact2831 : RatBall := localContactBall tau2831 center2831
def work2831 : RoundedTauEval :=
  evalTau precision tau2831 contact2831 logTwoBall

theorem center_sq2831 : (center2831.re : ℝ)^2 +
    (center2831.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2831]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2831 : work2831.theta.ok = true ∧
    work2831.jac.invOK = true ∧ acceptsUnitSq work2831.out = true := by
  norm_num [work2831, contact2831, tau2831, center2831, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2831 : CellCertificate where
  tauBall := tau2831
  contactCenter := center2831
  contactBall := contact2831
  work := work2831
  center_sq := center_sq2831
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2831.1
  jac_ok := checks2831.2.1
  accepted := checks2831.2.2

def cells : List CellCertificate := [cell2824, cell2825, cell2826, cell2827, cell2828, cell2829, cell2830, cell2831]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353
