import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2208 : RatBall :=
  ⟨⟨-3/320, 119/320⟩, 3/640⟩
def center2208 : GaussianRat :=
  ⟨-3793023/500000000, 135626627/500000000⟩
def contact2208 : RatBall := localContactBall tau2208 center2208
def work2208 : RoundedTauEval :=
  evalTau precision tau2208 contact2208 logTwoBall

theorem center_sq2208 : (center2208.re : ℝ)^2 +
    (center2208.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2208]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2208 : work2208.theta.ok = true ∧
    work2208.jac.invOK = true ∧ acceptsUnitSq work2208.out = true := by
  norm_num [work2208, contact2208, tau2208, center2208, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2208 : CellCertificate where
  tauBall := tau2208
  contactCenter := center2208
  contactBall := contact2208
  work := work2208
  center_sq := center_sq2208
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2208.1
  jac_ok := checks2208.2.1
  accepted := checks2208.2.2

def tau2209 : RatBall :=
  ⟨⟨-1/320, 119/320⟩, 3/640⟩
def center2209 : GaussianRat :=
  ⟨-1264407/500000000, 33910207/125000000⟩
def contact2209 : RatBall := localContactBall tau2209 center2209
def work2209 : RoundedTauEval :=
  evalTau precision tau2209 contact2209 logTwoBall

theorem center_sq2209 : (center2209.re : ℝ)^2 +
    (center2209.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2209]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2209 : work2209.theta.ok = true ∧
    work2209.jac.invOK = true ∧ acceptsUnitSq work2209.out = true := by
  norm_num [work2209, contact2209, tau2209, center2209, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2209 : CellCertificate where
  tauBall := tau2209
  contactCenter := center2209
  contactBall := contact2209
  work := work2209
  center_sq := center_sq2209
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2209.1
  jac_ok := checks2209.2.1
  accepted := checks2209.2.2

def tau2210 : RatBall :=
  ⟨⟨-3/64, 121/320⟩, 3/640⟩
def center2210 : GaussianRat :=
  ⟨-38091451/1000000000, 137769289/500000000⟩
def contact2210 : RatBall := localContactBall tau2210 center2210
def work2210 : RoundedTauEval :=
  evalTau precision tau2210 contact2210 logTwoBall

theorem center_sq2210 : (center2210.re : ℝ)^2 +
    (center2210.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2210]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2210 : work2210.theta.ok = true ∧
    work2210.jac.invOK = true ∧ acceptsUnitSq work2210.out = true := by
  norm_num [work2210, contact2210, tau2210, center2210, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2210 : CellCertificate where
  tauBall := tau2210
  contactCenter := center2210
  contactBall := contact2210
  work := work2210
  center_sq := center_sq2210
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2210.1
  jac_ok := checks2210.2.1
  accepted := checks2210.2.2

def tau2211 : RatBall :=
  ⟨⟨-13/320, 121/320⟩, 3/640⟩
def center2211 : GaussianRat :=
  ⟨-8256217/250000000, 34467723/125000000⟩
def contact2211 : RatBall := localContactBall tau2211 center2211
def work2211 : RoundedTauEval :=
  evalTau precision tau2211 contact2211 logTwoBall

theorem center_sq2211 : (center2211.re : ℝ)^2 +
    (center2211.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2211]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2211 : work2211.theta.ok = true ∧
    work2211.jac.invOK = true ∧ acceptsUnitSq work2211.out = true := by
  norm_num [work2211, contact2211, tau2211, center2211, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2211 : CellCertificate where
  tauBall := tau2211
  contactCenter := center2211
  contactBall := contact2211
  work := work2211
  center_sq := center_sq2211
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2211.1
  jac_ok := checks2211.2.1
  accepted := checks2211.2.2

def tau2212 : RatBall :=
  ⟨⟨-11/320, 121/320⟩, 3/640⟩
def center2212 : GaussianRat :=
  ⟨-27953037/1000000000, 55183249/200000000⟩
def contact2212 : RatBall := localContactBall tau2212 center2212
def work2212 : RoundedTauEval :=
  evalTau precision tau2212 contact2212 logTwoBall

theorem center_sq2212 : (center2212.re : ℝ)^2 +
    (center2212.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2212]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2212 : work2212.theta.ok = true ∧
    work2212.jac.invOK = true ∧ acceptsUnitSq work2212.out = true := by
  norm_num [work2212, contact2212, tau2212, center2212, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2212 : CellCertificate where
  tauBall := tau2212
  contactCenter := center2212
  contactBall := contact2212
  work := work2212
  center_sq := center_sq2212
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2212.1
  jac_ok := checks2212.2.1
  accepted := checks2212.2.2

def tau2213 : RatBall :=
  ⟨⟨-9/320, 121/320⟩, 3/640⟩
def center2213 : GaussianRat :=
  ⟨-4575351/200000000, 276061831/1000000000⟩
def contact2213 : RatBall := localContactBall tau2213 center2213
def work2213 : RoundedTauEval :=
  evalTau precision tau2213 contact2213 logTwoBall

theorem center_sq2213 : (center2213.re : ℝ)^2 +
    (center2213.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2213]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2213 : work2213.theta.ok = true ∧
    work2213.jac.invOK = true ∧ acceptsUnitSq work2213.out = true := by
  norm_num [work2213, contact2213, tau2213, center2213, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2213 : CellCertificate where
  tauBall := tau2213
  contactCenter := center2213
  contactBall := contact2213
  work := work2213
  center_sq := center_sq2213
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2213.1
  jac_ok := checks2213.2.1
  accepted := checks2213.2.2

def tau2214 : RatBall :=
  ⟨⟨-9/320, 123/320⟩, 3/640⟩
def center2214 : GaussianRat :=
  ⟨-11504853/500000000, 2811547/10000000⟩
def contact2214 : RatBall := localContactBall tau2214 center2214
def work2214 : RoundedTauEval :=
  evalTau precision tau2214 contact2214 logTwoBall

theorem center_sq2214 : (center2214.re : ℝ)^2 +
    (center2214.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2214]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2214 : work2214.theta.ok = true ∧
    work2214.jac.invOK = true ∧ acceptsUnitSq work2214.out = true := by
  norm_num [work2214, contact2214, tau2214, center2214, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2214 : CellCertificate where
  tauBall := tau2214
  contactCenter := center2214
  contactBall := contact2214
  work := work2214
  center_sq := center_sq2214
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2214.1
  jac_ok := checks2214.2.1
  accepted := checks2214.2.2

def tau2215 : RatBall :=
  ⟨⟨-7/320, 121/320⟩, 3/640⟩
def center2215 : GaussianRat :=
  ⟨-2224603/125000000, 539411/1953125⟩
def contact2215 : RatBall := localContactBall tau2215 center2215
def work2215 : RoundedTauEval :=
  evalTau precision tau2215 contact2215 logTwoBall

theorem center_sq2215 : (center2215.re : ℝ)^2 +
    (center2215.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2215]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2215 : work2215.theta.ok = true ∧
    work2215.jac.invOK = true ∧ acceptsUnitSq work2215.out = true := by
  norm_num [work2215, contact2215, tau2215, center2215, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2215 : CellCertificate where
  tauBall := tau2215
  contactCenter := center2215
  contactBall := contact2215
  work := work2215
  center_sq := center_sq2215
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2215.1
  jac_ok := checks2215.2.1
  accepted := checks2215.2.2

def cells : List CellCertificate := [cell2208, cell2209, cell2210, cell2211, cell2212, cell2213, cell2214, cell2215]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276
