import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0176 : RatBall :=
  ⟨⟨17/80, -1/16⟩, 3/160⟩
def center0176 : GaussianRat :=
  ⟨29119789/200000000, -10355411/250000000⟩
def contact0176 : RatBall := localContactBall tau0176 center0176
def work0176 : RoundedTauEval :=
  evalTau precision tau0176 contact0176 logTwoBall

theorem center_sq0176 : (center0176.re : ℝ)^2 +
    (center0176.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0176]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0176 : work0176.theta.ok = true ∧
    work0176.jac.invOK = true ∧ acceptsUnitSq work0176.out = true := by
  norm_num [work0176, contact0176, tau0176, center0176, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0176 : CellCertificate where
  tauBall := tau0176
  contactCenter := center0176
  contactBall := contact0176
  work := work0176
  center_sq := center_sq0176
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0176.1
  jac_ok := checks0176.2.1
  accepted := checks0176.2.2

def tau0177 : RatBall :=
  ⟨⟨19/80, -1/16⟩, 3/160⟩
def center0177 : GaussianRat :=
  ⟨81055451/500000000, -40960501/1000000000⟩
def contact0177 : RatBall := localContactBall tau0177 center0177
def work0177 : RoundedTauEval :=
  evalTau precision tau0177 contact0177 logTwoBall

theorem center_sq0177 : (center0177.re : ℝ)^2 +
    (center0177.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0177]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0177 : work0177.theta.ok = true ∧
    work0177.jac.invOK = true ∧ acceptsUnitSq work0177.out = true := by
  norm_num [work0177, contact0177, tau0177, center0177, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0177 : CellCertificate where
  tauBall := tau0177
  contactCenter := center0177
  contactBall := contact0177
  work := work0177
  center_sq := center_sq0177
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0177.1
  jac_ok := checks0177.2.1
  accepted := checks0177.2.2

def tau0178 : RatBall :=
  ⟨⟨21/80, -7/80⟩, 3/160⟩
def center0178 : GaussianRat :=
  ⟨17905297/100000000, -5669463/100000000⟩
def contact0178 : RatBall := localContactBall tau0178 center0178
def work0178 : RoundedTauEval :=
  evalTau precision tau0178 contact0178 logTwoBall

theorem center_sq0178 : (center0178.re : ℝ)^2 +
    (center0178.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0178]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0178 : work0178.theta.ok = true ∧
    work0178.jac.invOK = true ∧ acceptsUnitSq work0178.out = true := by
  norm_num [work0178, contact0178, tau0178, center0178, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0178 : CellCertificate where
  tauBall := tau0178
  contactCenter := center0178
  contactBall := contact0178
  work := work0178
  center_sq := center_sq0178
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0178.1
  jac_ok := checks0178.2.1
  accepted := checks0178.2.2

def tau0179 : RatBall :=
  ⟨⟨23/80, -7/80⟩, 3/160⟩
def center0179 : GaussianRat :=
  ⟨195201217/1000000000, -13984569/250000000⟩
def contact0179 : RatBall := localContactBall tau0179 center0179
def work0179 : RoundedTauEval :=
  evalTau precision tau0179 contact0179 logTwoBall

theorem center_sq0179 : (center0179.re : ℝ)^2 +
    (center0179.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0179]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0179 : work0179.theta.ok = true ∧
    work0179.jac.invOK = true ∧ acceptsUnitSq work0179.out = true := by
  norm_num [work0179, contact0179, tau0179, center0179, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0179 : CellCertificate where
  tauBall := tau0179
  contactCenter := center0179
  contactBall := contact0179
  work := work0179
  center_sq := center_sq0179
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0179.1
  jac_ok := checks0179.2.1
  accepted := checks0179.2.2

def tau0180 : RatBall :=
  ⟨⟨21/80, -1/16⟩, 3/160⟩
def center0180 : GaussianRat :=
  ⟨35685561/200000000, -40459851/1000000000⟩
def contact0180 : RatBall := localContactBall tau0180 center0180
def work0180 : RoundedTauEval :=
  evalTau precision tau0180 contact0180 logTwoBall

theorem center_sq0180 : (center0180.re : ℝ)^2 +
    (center0180.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0180]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0180 : work0180.theta.ok = true ∧
    work0180.jac.invOK = true ∧ acceptsUnitSq work0180.out = true := by
  norm_num [work0180, contact0180, tau0180, center0180, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0180 : CellCertificate where
  tauBall := tau0180
  contactCenter := center0180
  contactBall := contact0180
  work := work0180
  center_sq := center_sq0180
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0180.1
  jac_ok := checks0180.2.1
  accepted := checks0180.2.2

def tau0181 : RatBall :=
  ⟨⟨23/80, -1/16⟩, 3/160⟩
def center0181 : GaussianRat :=
  ⟨194534387/1000000000, -7984577/200000000⟩
def contact0181 : RatBall := localContactBall tau0181 center0181
def work0181 : RoundedTauEval :=
  evalTau precision tau0181 contact0181 logTwoBall

theorem center_sq0181 : (center0181.re : ℝ)^2 +
    (center0181.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0181]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0181 : work0181.theta.ok = true ∧
    work0181.jac.invOK = true ∧ acceptsUnitSq work0181.out = true := by
  norm_num [work0181, contact0181, tau0181, center0181, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0181 : CellCertificate where
  tauBall := tau0181
  contactCenter := center0181
  contactBall := contact0181
  work := work0181
  center_sq := center_sq0181
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0181.1
  jac_ok := checks0181.2.1
  accepted := checks0181.2.2

def tau0182 : RatBall :=
  ⟨⟨21/80, -3/80⟩, 3/160⟩
def center0182 : GaussianRat :=
  ⟨89006593/500000000, -4852281/200000000⟩
def contact0182 : RatBall := localContactBall tau0182 center0182
def work0182 : RoundedTauEval :=
  evalTau precision tau0182 contact0182 logTwoBall

theorem center_sq0182 : (center0182.re : ℝ)^2 +
    (center0182.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0182]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0182 : work0182.theta.ok = true ∧
    work0182.jac.invOK = true ∧ acceptsUnitSq work0182.out = true := by
  norm_num [work0182, contact0182, tau0182, center0182, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0182 : CellCertificate where
  tauBall := tau0182
  contactCenter := center0182
  contactBall := contact0182
  work := work0182
  center_sq := center_sq0182
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0182.1
  jac_ok := checks0182.2.1
  accepted := checks0182.2.2

def tau0183 : RatBall :=
  ⟨⟨23/80, -3/80⟩, 3/160⟩
def center0183 : GaussianRat :=
  ⟨4852301/25000000, -23940531/1000000000⟩
def contact0183 : RatBall := localContactBall tau0183 center0183
def work0183 : RoundedTauEval :=
  evalTau precision tau0183 contact0183 logTwoBall

theorem center_sq0183 : (center0183.re : ℝ)^2 +
    (center0183.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0183]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0183 : work0183.theta.ok = true ∧
    work0183.jac.invOK = true ∧ acceptsUnitSq work0183.out = true := by
  norm_num [work0183, contact0183, tau0183, center0183, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0183 : CellCertificate where
  tauBall := tau0183
  contactCenter := center0183
  contactBall := contact0183
  work := work0183
  center_sq := center_sq0183
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0183.1
  jac_ok := checks0183.2.1
  accepted := checks0183.2.2

def cells : List CellCertificate := [cell0176, cell0177, cell0178, cell0179, cell0180, cell0181, cell0182, cell0183]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022
