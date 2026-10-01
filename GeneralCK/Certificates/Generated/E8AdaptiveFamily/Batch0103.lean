import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0103

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0824 : RatBall :=
  ⟨⟨-49/160, 27/160⟩, 3/320⟩
def center0824 : GaussianRat :=
  ⟨-211098659/1000000000, 10718597/100000000⟩
def contact0824 : RatBall := localContactBall tau0824 center0824
def work0824 : RoundedTauEval :=
  evalTau precision tau0824 contact0824 logTwoBall

theorem center_sq0824 : (center0824.re : ℝ)^2 +
    (center0824.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0824]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0824 : work0824.theta.ok = true ∧
    work0824.jac.invOK = true ∧ acceptsUnitSq work0824.out = true := by
  norm_num [work0824, contact0824, tau0824, center0824, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0824 : CellCertificate where
  tauBall := tau0824
  contactCenter := center0824
  contactBall := contact0824
  work := work0824
  center_sq := center_sq0824
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0824.1
  jac_ok := checks0824.2.1
  accepted := checks0824.2.2

def tau0825 : RatBall :=
  ⟨⟨-11/32, 29/160⟩, 3/320⟩
def center0825 : GaussianRat :=
  ⟨-117898859/500000000, 112506293/1000000000⟩
def contact0825 : RatBall := localContactBall tau0825 center0825
def work0825 : RoundedTauEval :=
  evalTau precision tau0825 contact0825 logTwoBall

theorem center_sq0825 : (center0825.re : ℝ)^2 +
    (center0825.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0825]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0825 : work0825.theta.ok = true ∧
    work0825.jac.invOK = true ∧ acceptsUnitSq work0825.out = true := by
  norm_num [work0825, contact0825, tau0825, center0825, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0825 : CellCertificate where
  tauBall := tau0825
  contactCenter := center0825
  contactBall := contact0825
  work := work0825
  center_sq := center_sq0825
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0825.1
  jac_ok := checks0825.2.1
  accepted := checks0825.2.2

def tau0826 : RatBall :=
  ⟨⟨-53/160, 29/160⟩, 3/320⟩
def center0826 : GaussianRat :=
  ⟨-227914773/1000000000, 56716957/500000000⟩
def contact0826 : RatBall := localContactBall tau0826 center0826
def work0826 : RoundedTauEval :=
  evalTau precision tau0826 contact0826 logTwoBall

theorem center_sq0826 : (center0826.re : ℝ)^2 +
    (center0826.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0826]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0826 : work0826.theta.ok = true ∧
    work0826.jac.invOK = true ∧ acceptsUnitSq work0826.out = true := by
  norm_num [work0826, contact0826, tau0826, center0826, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0826 : CellCertificate where
  tauBall := tau0826
  contactCenter := center0826
  contactBall := contact0826
  work := work0826
  center_sq := center_sq0826
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0826.1
  jac_ok := checks0826.2.1
  accepted := checks0826.2.2

def tau0827 : RatBall :=
  ⟨⟨-11/32, 31/160⟩, 3/320⟩
def center0827 : GaussianRat :=
  ⟨-47354053/200000000, 30090849/250000000⟩
def contact0827 : RatBall := localContactBall tau0827 center0827
def work0827 : RoundedTauEval :=
  evalTau precision tau0827 contact0827 logTwoBall

theorem center_sq0827 : (center0827.re : ℝ)^2 +
    (center0827.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0827]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0827 : work0827.theta.ok = true ∧
    work0827.jac.invOK = true ∧ acceptsUnitSq work0827.out = true := by
  norm_num [work0827, contact0827, tau0827, center0827, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0827 : CellCertificate where
  tauBall := tau0827
  contactCenter := center0827
  contactBall := contact0827
  work := work0827
  center_sq := center_sq0827
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0827.1
  jac_ok := checks0827.2.1
  accepted := checks0827.2.2

def tau0828 : RatBall :=
  ⟨⟨-53/160, 31/160⟩, 3/320⟩
def center0828 : GaussianRat :=
  ⟨-114433899/500000000, 30340451/250000000⟩
def contact0828 : RatBall := localContactBall tau0828 center0828
def work0828 : RoundedTauEval :=
  evalTau precision tau0828 contact0828 logTwoBall

theorem center_sq0828 : (center0828.re : ℝ)^2 +
    (center0828.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0828]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0828 : work0828.theta.ok = true ∧
    work0828.jac.invOK = true ∧ acceptsUnitSq work0828.out = true := by
  norm_num [work0828, contact0828, tau0828, center0828, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0828 : CellCertificate where
  tauBall := tau0828
  contactCenter := center0828
  contactBall := contact0828
  work := work0828
  center_sq := center_sq0828
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0828.1
  jac_ok := checks0828.2.1
  accepted := checks0828.2.2

def tau0829 : RatBall :=
  ⟨⟨-51/160, 29/160⟩, 3/320⟩
def center0829 : GaussianRat :=
  ⟨-429614/1953125, 114341983/1000000000⟩
def contact0829 : RatBall := localContactBall tau0829 center0829
def work0829 : RoundedTauEval :=
  evalTau precision tau0829 contact0829 logTwoBall

theorem center_sq0829 : (center0829.re : ℝ)^2 +
    (center0829.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0829]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0829 : work0829.theta.ok = true ∧
    work0829.jac.invOK = true ∧ acceptsUnitSq work0829.out = true := by
  norm_num [work0829, contact0829, tau0829, center0829, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0829 : CellCertificate where
  tauBall := tau0829
  contactCenter := center0829
  contactBall := contact0829
  work := work0829
  center_sq := center_sq0829
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0829.1
  jac_ok := checks0829.2.1
  accepted := checks0829.2.2

def tau0830 : RatBall :=
  ⟨⟨-49/160, 29/160⟩, 3/320⟩
def center0830 : GaussianRat :=
  ⟨-52985469/250000000, 115229173/1000000000⟩
def contact0830 : RatBall := localContactBall tau0830 center0830
def work0830 : RoundedTauEval :=
  evalTau precision tau0830 contact0830 logTwoBall

theorem center_sq0830 : (center0830.re : ℝ)^2 +
    (center0830.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0830]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0830 : work0830.theta.ok = true ∧
    work0830.jac.invOK = true ∧ acceptsUnitSq work0830.out = true := by
  norm_num [work0830, contact0830, tau0830, center0830, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0830 : CellCertificate where
  tauBall := tau0830
  contactCenter := center0830
  contactBall := contact0830
  work := work0830
  center_sq := center_sq0830
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0830.1
  jac_ok := checks0830.2.1
  accepted := checks0830.2.2

def tau0831 : RatBall :=
  ⟨⟨-51/160, 31/160⟩, 3/320⟩
def center0831 : GaussianRat :=
  ⟨-110447247/500000000, 61169673/500000000⟩
def contact0831 : RatBall := localContactBall tau0831 center0831
def work0831 : RoundedTauEval :=
  evalTau precision tau0831 contact0831 logTwoBall

theorem center_sq0831 : (center0831.re : ℝ)^2 +
    (center0831.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0831]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0831 : work0831.theta.ok = true ∧
    work0831.jac.invOK = true ∧ acceptsUnitSq work0831.out = true := by
  norm_num [work0831, contact0831, tau0831, center0831, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0831 : CellCertificate where
  tauBall := tau0831
  contactCenter := center0831
  contactBall := contact0831
  work := work0831
  center_sq := center_sq0831
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0831.1
  jac_ok := checks0831.2.1
  accepted := checks0831.2.2

def cells : List CellCertificate := [cell0824, cell0825, cell0826, cell0827, cell0828, cell0829, cell0830, cell0831]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0103
