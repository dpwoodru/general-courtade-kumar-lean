import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0160 : RatBall :=
  ⟨⟨3/16, -9/80⟩, 3/160⟩
def center0160 : GaussianRat :=
  ⟨26005447/200000000, -37751763/500000000⟩
def contact0160 : RatBall := localContactBall tau0160 center0160
def work0160 : RoundedTauEval :=
  evalTau precision tau0160 contact0160 logTwoBall

theorem center_sq0160 : (center0160.re : ℝ)^2 +
    (center0160.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0160]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0160 : work0160.theta.ok = true ∧
    work0160.jac.invOK = true ∧ acceptsUnitSq work0160.out = true := by
  norm_num [work0160, contact0160, tau0160, center0160, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0160 : CellCertificate where
  tauBall := tau0160
  contactCenter := center0160
  contactBall := contact0160
  work := work0160
  center_sq := center_sq0160
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0160.1
  jac_ok := checks0160.2.1
  accepted := checks0160.2.2

def tau0161 : RatBall :=
  ⟨⟨17/80, -3/16⟩, 3/160⟩
def center0161 : GaussianRat :=
  ⟨150128589/1000000000, -25067823/200000000⟩
def contact0161 : RatBall := localContactBall tau0161 center0161
def work0161 : RoundedTauEval :=
  evalTau precision tau0161 contact0161 logTwoBall

theorem center_sq0161 : (center0161.re : ℝ)^2 +
    (center0161.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0161]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0161 : work0161.theta.ok = true ∧
    work0161.jac.invOK = true ∧ acceptsUnitSq work0161.out = true := by
  norm_num [work0161, contact0161, tau0161, center0161, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0161 : CellCertificate where
  tauBall := tau0161
  contactCenter := center0161
  contactBall := contact0161
  work := work0161
  center_sq := center_sq0161
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0161.1
  jac_ok := checks0161.2.1
  accepted := checks0161.2.2

def tau0162 : RatBall :=
  ⟨⟨17/80, -13/80⟩, 3/160⟩
def center0162 : GaussianRat :=
  ⟨148834391/1000000000, -27091123/250000000⟩
def contact0162 : RatBall := localContactBall tau0162 center0162
def work0162 : RoundedTauEval :=
  evalTau precision tau0162 contact0162 logTwoBall

theorem center_sq0162 : (center0162.re : ℝ)^2 +
    (center0162.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0162]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0162 : work0162.theta.ok = true ∧
    work0162.jac.invOK = true ∧ acceptsUnitSq work0162.out = true := by
  norm_num [work0162, contact0162, tau0162, center0162, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0162 : CellCertificate where
  tauBall := tau0162
  contactCenter := center0162
  contactBall := contact0162
  work := work0162
  center_sq := center_sq0162
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0162.1
  jac_ok := checks0162.2.1
  accepted := checks0162.2.2

def tau0163 : RatBall :=
  ⟨⟨19/80, -13/80⟩, 3/160⟩
def center0163 : GaussianRat :=
  ⟨41411389/250000000, -107116873/1000000000⟩
def contact0163 : RatBall := localContactBall tau0163 center0163
def work0163 : RoundedTauEval :=
  evalTau precision tau0163 contact0163 logTwoBall

theorem center_sq0163 : (center0163.re : ℝ)^2 +
    (center0163.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0163]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0163 : work0163.theta.ok = true ∧
    work0163.jac.invOK = true ∧ acceptsUnitSq work0163.out = true := by
  norm_num [work0163, contact0163, tau0163, center0163, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0163 : CellCertificate where
  tauBall := tau0163
  contactCenter := center0163
  contactBall := contact0163
  work := work0163
  center_sq := center_sq0163
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0163.1
  jac_ok := checks0163.2.1
  accepted := checks0163.2.2

def tau0164 : RatBall :=
  ⟨⟨21/80, -13/80⟩, 3/160⟩
def center0164 : GaussianRat :=
  ⟨4555953/25000000, -105764329/1000000000⟩
def contact0164 : RatBall := localContactBall tau0164 center0164
def work0164 : RoundedTauEval :=
  evalTau precision tau0164 contact0164 logTwoBall

theorem center_sq0164 : (center0164.re : ℝ)^2 +
    (center0164.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0164]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0164 : work0164.theta.ok = true ∧
    work0164.jac.invOK = true ∧ acceptsUnitSq work0164.out = true := by
  norm_num [work0164, contact0164, tau0164, center0164, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0164 : CellCertificate where
  tauBall := tau0164
  contactCenter := center0164
  contactBall := contact0164
  work := work0164
  center_sq := center_sq0164
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0164.1
  jac_ok := checks0164.2.1
  accepted := checks0164.2.2

def tau0165 : RatBall :=
  ⟨⟨17/80, -11/80⟩, 3/160⟩
def center0165 : GaussianRat :=
  ⟨1154229/7812500, -91503559/1000000000⟩
def contact0165 : RatBall := localContactBall tau0165 center0165
def work0165 : RoundedTauEval :=
  evalTau precision tau0165 contact0165 logTwoBall

theorem center_sq0165 : (center0165.re : ℝ)^2 +
    (center0165.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0165]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0165 : work0165.theta.ok = true ∧
    work0165.jac.invOK = true ∧ acceptsUnitSq work0165.out = true := by
  norm_num [work0165, contact0165, tau0165, center0165, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0165 : CellCertificate where
  tauBall := tau0165
  contactCenter := center0165
  contactBall := contact0165
  work := work0165
  center_sq := center_sq0165
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0165.1
  jac_ok := checks0165.2.1
  accepted := checks0165.2.2

def tau0166 : RatBall :=
  ⟨⟨19/80, -11/80⟩, 3/160⟩
def center0166 : GaussianRat :=
  ⟨82225973/500000000, -18092371/200000000⟩
def contact0166 : RatBall := localContactBall tau0166 center0166
def work0166 : RoundedTauEval :=
  evalTau precision tau0166 contact0166 logTwoBall

theorem center_sq0166 : (center0166.re : ℝ)^2 +
    (center0166.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0166]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0166 : work0166.theta.ok = true ∧
    work0166.jac.invOK = true ∧ acceptsUnitSq work0166.out = true := by
  norm_num [work0166, contact0166, tau0166, center0166, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0166 : CellCertificate where
  tauBall := tau0166
  contactCenter := center0166
  contactBall := contact0166
  work := work0166
  center_sq := center_sq0166
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0166.1
  jac_ok := checks0166.2.1
  accepted := checks0166.2.2

def tau0167 : RatBall :=
  ⟨⟨17/80, -9/80⟩, 3/160⟩
def center0167 : GaussianRat :=
  ⟨29368329/200000000, -18684497/250000000⟩
def contact0167 : RatBall := localContactBall tau0167 center0167
def work0167 : RoundedTauEval :=
  evalTau precision tau0167 contact0167 logTwoBall

theorem center_sq0167 : (center0167.re : ℝ)^2 +
    (center0167.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0167]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0167 : work0167.theta.ok = true ∧
    work0167.jac.invOK = true ∧ acceptsUnitSq work0167.out = true := by
  norm_num [work0167, contact0167, tau0167, center0167, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0167 : CellCertificate where
  tauBall := tau0167
  contactCenter := center0167
  contactBall := contact0167
  work := work0167
  center_sq := center_sq0167
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0167.1
  jac_ok := checks0167.2.1
  accepted := checks0167.2.2

def cells : List CellCertificate := [cell0160, cell0161, cell0162, cell0163, cell0164, cell0165, cell0166, cell0167]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020
