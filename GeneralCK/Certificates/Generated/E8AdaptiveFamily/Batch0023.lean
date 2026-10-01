import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0184 : RatBall :=
  ⟨⟨21/80, -1/80⟩, 3/160⟩
def center0184 : GaussianRat :=
  ⟨4445163/25000000, -8084719/1000000000⟩
def contact0184 : RatBall := localContactBall tau0184 center0184
def work0184 : RoundedTauEval :=
  evalTau precision tau0184 contact0184 logTwoBall

theorem center_sq0184 : (center0184.re : ℝ)^2 +
    (center0184.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0184]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0184 : work0184.theta.ok = true ∧
    work0184.jac.invOK = true ∧ acceptsUnitSq work0184.out = true := by
  norm_num [work0184, contact0184, tau0184, center0184, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0184 : CellCertificate where
  tauBall := tau0184
  contactCenter := center0184
  contactBall := contact0184
  work := work0184
  center_sq := center_sq0184
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0184.1
  jac_ok := checks0184.2.1
  accepted := checks0184.2.2

def tau0185 : RatBall :=
  ⟨⟨23/80, -1/80⟩, 3/160⟩
def center0185 : GaussianRat :=
  ⟨7754861/40000000, -3988989/500000000⟩
def contact0185 : RatBall := localContactBall tau0185 center0185
def work0185 : RoundedTauEval :=
  evalTau precision tau0185 contact0185 logTwoBall

theorem center_sq0185 : (center0185.re : ℝ)^2 +
    (center0185.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0185]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0185 : work0185.theta.ok = true ∧
    work0185.jac.invOK = true ∧ acceptsUnitSq work0185.out = true := by
  norm_num [work0185, contact0185, tau0185, center0185, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0185 : CellCertificate where
  tauBall := tau0185
  contactCenter := center0185
  contactBall := contact0185
  work := work0185
  center_sq := center_sq0185
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0185.1
  jac_ok := checks0185.2.1
  accepted := checks0185.2.2

def tau0186 : RatBall :=
  ⟨⟨5/16, -7/80⟩, 3/160⟩
def center0186 : GaussianRat :=
  ⟨211121197/1000000000, -55135609/1000000000⟩
def contact0186 : RatBall := localContactBall tau0186 center0186
def work0186 : RoundedTauEval :=
  evalTau precision tau0186 contact0186 logTwoBall

theorem center_sq0186 : (center0186.re : ℝ)^2 +
    (center0186.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0186]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0186 : work0186.theta.ok = true ∧
    work0186.jac.invOK = true ∧ acceptsUnitSq work0186.out = true := by
  norm_num [work0186, contact0186, tau0186, center0186, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0186 : CellCertificate where
  tauBall := tau0186
  contactCenter := center0186
  contactBall := contact0186
  work := work0186
  center_sq := center_sq0186
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0186.1
  jac_ok := checks0186.2.1
  accepted := checks0186.2.2

def tau0187 : RatBall :=
  ⟨⟨27/80, -7/80⟩, 3/160⟩
def center0187 : GaussianRat :=
  ⟨14175019/62500000, -54291363/1000000000⟩
def contact0187 : RatBall := localContactBall tau0187 center0187
def work0187 : RoundedTauEval :=
  evalTau precision tau0187 contact0187 logTwoBall

theorem center_sq0187 : (center0187.re : ℝ)^2 +
    (center0187.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0187]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0187 : work0187.theta.ok = true ∧
    work0187.jac.invOK = true ∧ acceptsUnitSq work0187.out = true := by
  norm_num [work0187, contact0187, tau0187, center0187, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0187 : CellCertificate where
  tauBall := tau0187
  contactCenter := center0187
  contactBall := contact0187
  work := work0187
  center_sq := center_sq0187
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0187.1
  jac_ok := checks0187.2.1
  accepted := checks0187.2.2

def tau0188 : RatBall :=
  ⟨⟨5/16, -1/16⟩, 3/160⟩
def center0188 : GaussianRat :=
  ⟨26302089/125000000, -3935289/100000000⟩
def contact0188 : RatBall := localContactBall tau0188 center0188
def work0188 : RoundedTauEval :=
  evalTau precision tau0188 contact0188 logTwoBall

theorem center_sq0188 : (center0188.re : ℝ)^2 +
    (center0188.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0188]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0188 : work0188.theta.ok = true ∧
    work0188.jac.invOK = true ∧ acceptsUnitSq work0188.out = true := by
  norm_num [work0188, contact0188, tau0188, center0188, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0188 : CellCertificate where
  tauBall := tau0188
  contactCenter := center0188
  contactBall := contact0188
  work := work0188
  center_sq := center_sq0188
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0188.1
  jac_ok := checks0188.2.1
  accepted := checks0188.2.2

def tau0189 : RatBall :=
  ⟨⟨27/80, -1/16⟩, 3/160⟩
def center0189 : GaussianRat :=
  ⟨22606221/100000000, -4844151/125000000⟩
def contact0189 : RatBall := localContactBall tau0189 center0189
def work0189 : RoundedTauEval :=
  evalTau precision tau0189 contact0189 logTwoBall

theorem center_sq0189 : (center0189.re : ℝ)^2 +
    (center0189.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0189]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0189 : work0189.theta.ok = true ∧
    work0189.jac.invOK = true ∧ acceptsUnitSq work0189.out = true := by
  norm_num [work0189, contact0189, tau0189, center0189, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0189 : CellCertificate where
  tauBall := tau0189
  contactCenter := center0189
  contactBall := contact0189
  work := work0189
  center_sq := center_sq0189
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0189.1
  jac_ok := checks0189.2.1
  accepted := checks0189.2.2

def tau0190 : RatBall :=
  ⟨⟨29/80, -1/16⟩, 3/160⟩
def center0190 : GaussianRat :=
  ⟨241459683/1000000000, -9531797/250000000⟩
def contact0190 : RatBall := localContactBall tau0190 center0190
def work0190 : RoundedTauEval :=
  evalTau precision tau0190 contact0190 logTwoBall

theorem center_sq0190 : (center0190.re : ℝ)^2 +
    (center0190.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0190]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0190 : work0190.theta.ok = true ∧
    work0190.jac.invOK = true ∧ acceptsUnitSq work0190.out = true := by
  norm_num [work0190, contact0190, tau0190, center0190, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0190 : CellCertificate where
  tauBall := tau0190
  contactCenter := center0190
  contactBall := contact0190
  work := work0190
  center_sq := center_sq0190
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0190.1
  jac_ok := checks0190.2.1
  accepted := checks0190.2.2

def tau0191 : RatBall :=
  ⟨⟨5/16, -3/80⟩, 3/160⟩
def center0191 : GaussianRat :=
  ⟨209949283/1000000000, -11799931/500000000⟩
def contact0191 : RatBall := localContactBall tau0191 center0191
def work0191 : RoundedTauEval :=
  evalTau precision tau0191 contact0191 logTwoBall

theorem center_sq0191 : (center0191.re : ℝ)^2 +
    (center0191.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0191]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0191 : work0191.theta.ok = true ∧
    work0191.jac.invOK = true ∧ acceptsUnitSq work0191.out = true := by
  norm_num [work0191, contact0191, tau0191, center0191, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0191 : CellCertificate where
  tauBall := tau0191
  contactCenter := center0191
  contactBall := contact0191
  work := work0191
  center_sq := center_sq0191
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0191.1
  jac_ok := checks0191.2.1
  accepted := checks0191.2.2

def cells : List CellCertificate := [cell0184, cell0185, cell0186, cell0187, cell0188, cell0189, cell0190, cell0191]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023
