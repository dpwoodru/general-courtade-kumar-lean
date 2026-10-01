import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0168 : RatBall :=
  ⟨⟨19/80, -9/80⟩, 3/160⟩
def center0168 : GaussianRat :=
  ⟨163469111/1000000000, -36947527/500000000⟩
def contact0168 : RatBall := localContactBall tau0168 center0168
def work0168 : RoundedTauEval :=
  evalTau precision tau0168 contact0168 logTwoBall

theorem center_sq0168 : (center0168.re : ℝ)^2 +
    (center0168.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0168]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0168 : work0168.theta.ok = true ∧
    work0168.jac.invOK = true ∧ acceptsUnitSq work0168.out = true := by
  norm_num [work0168, contact0168, tau0168, center0168, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0168 : CellCertificate where
  tauBall := tau0168
  contactCenter := center0168
  contactBall := contact0168
  work := work0168
  center_sq := center_sq0168
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0168.1
  jac_ok := checks0168.2.1
  accepted := checks0168.2.2

def tau0169 : RatBall :=
  ⟨⟨21/80, -11/80⟩, 3/160⟩
def center0169 : GaussianRat :=
  ⟨90476031/500000000, -89331987/1000000000⟩
def contact0169 : RatBall := localContactBall tau0169 center0169
def work0169 : RoundedTauEval :=
  evalTau precision tau0169 contact0169 logTwoBall

theorem center_sq0169 : (center0169.re : ℝ)^2 +
    (center0169.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0169]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0169 : work0169.theta.ok = true ∧
    work0169.jac.invOK = true ∧ acceptsUnitSq work0169.out = true := by
  norm_num [work0169, contact0169, tau0169, center0169, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0169 : CellCertificate where
  tauBall := tau0169
  contactCenter := center0169
  contactBall := contact0169
  work := work0169
  center_sq := center_sq0169
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0169.1
  jac_ok := checks0169.2.1
  accepted := checks0169.2.2

def tau0170 : RatBall :=
  ⟨⟨23/80, -11/80⟩, 3/160⟩
def center0170 : GaussianRat :=
  ⟨19722583/100000000, -88121387/1000000000⟩
def contact0170 : RatBall := localContactBall tau0170 center0170
def work0170 : RoundedTauEval :=
  evalTau precision tau0170 contact0170 logTwoBall

theorem center_sq0170 : (center0170.re : ℝ)^2 +
    (center0170.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0170]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0170 : work0170.theta.ok = true ∧
    work0170.jac.invOK = true ∧ acceptsUnitSq work0170.out = true := by
  norm_num [work0170, contact0170, tau0170, center0170, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0170 : CellCertificate where
  tauBall := tau0170
  contactCenter := center0170
  contactBall := contact0170
  work := work0170
  center_sq := center_sq0170
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0170.1
  jac_ok := checks0170.2.1
  accepted := checks0170.2.2

def tau0171 : RatBall :=
  ⟨⟨21/80, -9/80⟩, 3/160⟩
def center0171 : GaussianRat :=
  ⟨44973153/250000000, -72980409/1000000000⟩
def contact0171 : RatBall := localContactBall tau0171 center0171
def work0171 : RoundedTauEval :=
  evalTau precision tau0171 contact0171 logTwoBall

theorem center_sq0171 : (center0171.re : ℝ)^2 +
    (center0171.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0171]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0171 : work0171.theta.ok = true ∧
    work0171.jac.invOK = true ∧ acceptsUnitSq work0171.out = true := by
  norm_num [work0171, contact0171, tau0171, center0171, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0171 : CellCertificate where
  tauBall := tau0171
  contactCenter := center0171
  contactBall := contact0171
  work := work0171
  center_sq := center_sq0171
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0171.1
  jac_ok := checks0171.2.1
  accepted := checks0171.2.2

def tau0172 : RatBall :=
  ⟨⟨23/80, -9/80⟩, 3/160⟩
def center0172 : GaussianRat :=
  ⟨196096551/1000000000, -71999991/1000000000⟩
def contact0172 : RatBall := localContactBall tau0172 center0172
def work0172 : RoundedTauEval :=
  evalTau precision tau0172 contact0172 logTwoBall

theorem center_sq0172 : (center0172.re : ℝ)^2 +
    (center0172.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0172]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0172 : work0172.theta.ok = true ∧
    work0172.jac.invOK = true ∧ acceptsUnitSq work0172.out = true := by
  norm_num [work0172, contact0172, tau0172, center0172, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0172 : CellCertificate where
  tauBall := tau0172
  contactCenter := center0172
  contactBall := contact0172
  work := work0172
  center_sq := center_sq0172
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0172.1
  jac_ok := checks0172.2.1
  accepted := checks0172.2.2

def tau0173 : RatBall :=
  ⟨⟨5/16, -9/80⟩, 3/160⟩
def center0173 : GaussianRat :=
  ⟨106033397/500000000, -70959907/1000000000⟩
def contact0173 : RatBall := localContactBall tau0173 center0173
def work0173 : RoundedTauEval :=
  evalTau precision tau0173 contact0173 logTwoBall

theorem center_sq0173 : (center0173.re : ℝ)^2 +
    (center0173.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0173]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0173 : work0173.theta.ok = true ∧
    work0173.jac.invOK = true ∧ acceptsUnitSq work0173.out = true := by
  norm_num [work0173, contact0173, tau0173, center0173, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0173 : CellCertificate where
  tauBall := tau0173
  contactCenter := center0173
  contactBall := contact0173
  work := work0173
  center_sq := center_sq0173
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0173.1
  jac_ok := checks0173.2.1
  accepted := checks0173.2.2

def tau0174 : RatBall :=
  ⟨⟨17/80, -7/80⟩, 3/160⟩
def center0174 : GaussianRat :=
  ⟨146129149/1000000000, -3628117/62500000⟩
def contact0174 : RatBall := localContactBall tau0174 center0174
def work0174 : RoundedTauEval :=
  evalTau precision tau0174 contact0174 logTwoBall

theorem center_sq0174 : (center0174.re : ℝ)^2 +
    (center0174.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0174]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0174 : work0174.theta.ok = true ∧
    work0174.jac.invOK = true ∧ acceptsUnitSq work0174.out = true := by
  norm_num [work0174, contact0174, tau0174, center0174, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0174 : CellCertificate where
  tauBall := tau0174
  contactCenter := center0174
  contactBall := contact0174
  work := work0174
  center_sq := center_sq0174
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0174.1
  jac_ok := checks0174.2.1
  accepted := checks0174.2.2

def tau0175 : RatBall :=
  ⟨⟨19/80, -7/80⟩, 3/160⟩
def center0175 : GaussianRat :=
  ⟨162690477/1000000000, -28700003/500000000⟩
def contact0175 : RatBall := localContactBall tau0175 center0175
def work0175 : RoundedTauEval :=
  evalTau precision tau0175 contact0175 logTwoBall

theorem center_sq0175 : (center0175.re : ℝ)^2 +
    (center0175.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0175]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0175 : work0175.theta.ok = true ∧
    work0175.jac.invOK = true ∧ acceptsUnitSq work0175.out = true := by
  norm_num [work0175, contact0175, tau0175, center0175, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0175 : CellCertificate where
  tauBall := tau0175
  contactCenter := center0175
  contactBall := contact0175
  work := work0175
  center_sq := center_sq0175
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0175.1
  jac_ok := checks0175.2.1
  accepted := checks0175.2.2

def cells : List CellCertificate := [cell0168, cell0169, cell0170, cell0171, cell0172, cell0173, cell0174, cell0175]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021
