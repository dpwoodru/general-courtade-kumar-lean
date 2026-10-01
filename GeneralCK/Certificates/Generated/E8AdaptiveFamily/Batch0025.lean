import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0200 : RatBall :=
  ⟨⟨-29/80, 3/80⟩, 3/160⟩
def center0200 : GaussianRat :=
  ⟨-120475049/500000000, 4573419/200000000⟩
def contact0200 : RatBall := localContactBall tau0200 center0200
def work0200 : RoundedTauEval :=
  evalTau precision tau0200 contact0200 logTwoBall

theorem center_sq0200 : (center0200.re : ℝ)^2 +
    (center0200.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0200]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0200 : work0200.theta.ok = true ∧
    work0200.jac.invOK = true ∧ acceptsUnitSq work0200.out = true := by
  norm_num [work0200, contact0200, tau0200, center0200, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0200 : CellCertificate where
  tauBall := tau0200
  contactCenter := center0200
  contactBall := contact0200
  work := work0200
  center_sq := center_sq0200
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0200.1
  jac_ok := checks0200.2.1
  accepted := checks0200.2.2

def tau0201 : RatBall :=
  ⟨⟨-27/80, 1/80⟩, 3/160⟩
def center0201 : GaussianRat :=
  ⟨-45065623/200000000, 7745371/1000000000⟩
def contact0201 : RatBall := localContactBall tau0201 center0201
def work0201 : RoundedTauEval :=
  evalTau precision tau0201 contact0201 logTwoBall

theorem center_sq0201 : (center0201.re : ℝ)^2 +
    (center0201.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0201]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0201 : work0201.theta.ok = true ∧
    work0201.jac.invOK = true ∧ acceptsUnitSq work0201.out = true := by
  norm_num [work0201, contact0201, tau0201, center0201, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0201 : CellCertificate where
  tauBall := tau0201
  contactCenter := center0201
  contactBall := contact0201
  work := work0201
  center_sq := center_sq0201
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0201.1
  jac_ok := checks0201.2.1
  accepted := checks0201.2.2

def tau0202 : RatBall :=
  ⟨⟨-5/16, 1/80⟩, 3/160⟩
def center0202 : GaussianRat :=
  ⟨-104858117/500000000, 3932321/500000000⟩
def contact0202 : RatBall := localContactBall tau0202 center0202
def work0202 : RoundedTauEval :=
  evalTau precision tau0202 contact0202 logTwoBall

theorem center_sq0202 : (center0202.re : ℝ)^2 +
    (center0202.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0202]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0202 : work0202.theta.ok = true ∧
    work0202.jac.invOK = true ∧ acceptsUnitSq work0202.out = true := by
  norm_num [work0202, contact0202, tau0202, center0202, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0202 : CellCertificate where
  tauBall := tau0202
  contactCenter := center0202
  contactBall := contact0202
  work := work0202
  center_sq := center_sq0202
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0202.1
  jac_ok := checks0202.2.1
  accepted := checks0202.2.2

def tau0203 : RatBall :=
  ⟨⟨-27/80, 3/80⟩, 3/160⟩
def center0203 : GaussianRat :=
  ⟨-225572371/1000000000, 4648277/200000000⟩
def contact0203 : RatBall := localContactBall tau0203 center0203
def work0203 : RoundedTauEval :=
  evalTau precision tau0203 contact0203 logTwoBall

theorem center_sq0203 : (center0203.re : ℝ)^2 +
    (center0203.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0203]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0203 : work0203.theta.ok = true ∧
    work0203.jac.invOK = true ∧ acceptsUnitSq work0203.out = true := by
  norm_num [work0203, contact0203, tau0203, center0203, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0203 : CellCertificate where
  tauBall := tau0203
  contactCenter := center0203
  contactBall := contact0203
  work := work0203
  center_sq := center_sq0203
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0203.1
  jac_ok := checks0203.2.1
  accepted := checks0203.2.2

def tau0204 : RatBall :=
  ⟨⟨-5/16, 3/80⟩, 3/160⟩
def center0204 : GaussianRat :=
  ⟨-209949283/1000000000, 11799931/500000000⟩
def contact0204 : RatBall := localContactBall tau0204 center0204
def work0204 : RoundedTauEval :=
  evalTau precision tau0204 contact0204 logTwoBall

theorem center_sq0204 : (center0204.re : ℝ)^2 +
    (center0204.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0204]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0204 : work0204.theta.ok = true ∧
    work0204.jac.invOK = true ∧ acceptsUnitSq work0204.out = true := by
  norm_num [work0204, contact0204, tau0204, center0204, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0204 : CellCertificate where
  tauBall := tau0204
  contactCenter := center0204
  contactBall := contact0204
  work := work0204
  center_sq := center_sq0204
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0204.1
  jac_ok := checks0204.2.1
  accepted := checks0204.2.2

def tau0205 : RatBall :=
  ⟨⟨-29/80, 1/16⟩, 3/160⟩
def center0205 : GaussianRat :=
  ⟨-241459683/1000000000, 9531797/250000000⟩
def contact0205 : RatBall := localContactBall tau0205 center0205
def work0205 : RoundedTauEval :=
  evalTau precision tau0205 contact0205 logTwoBall

theorem center_sq0205 : (center0205.re : ℝ)^2 +
    (center0205.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0205]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0205 : work0205.theta.ok = true ∧
    work0205.jac.invOK = true ∧ acceptsUnitSq work0205.out = true := by
  norm_num [work0205, contact0205, tau0205, center0205, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0205 : CellCertificate where
  tauBall := tau0205
  contactCenter := center0205
  contactBall := contact0205
  work := work0205
  center_sq := center_sq0205
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0205.1
  jac_ok := checks0205.2.1
  accepted := checks0205.2.2

def tau0206 : RatBall :=
  ⟨⟨-27/80, 1/16⟩, 3/160⟩
def center0206 : GaussianRat :=
  ⟨-22606221/100000000, 4844151/125000000⟩
def contact0206 : RatBall := localContactBall tau0206 center0206
def work0206 : RoundedTauEval :=
  evalTau precision tau0206 contact0206 logTwoBall

theorem center_sq0206 : (center0206.re : ℝ)^2 +
    (center0206.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0206]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0206 : work0206.theta.ok = true ∧
    work0206.jac.invOK = true ∧ acceptsUnitSq work0206.out = true := by
  norm_num [work0206, contact0206, tau0206, center0206, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0206 : CellCertificate where
  tauBall := tau0206
  contactCenter := center0206
  contactBall := contact0206
  work := work0206
  center_sq := center_sq0206
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0206.1
  jac_ok := checks0206.2.1
  accepted := checks0206.2.2

def tau0207 : RatBall :=
  ⟨⟨-5/16, 1/16⟩, 3/160⟩
def center0207 : GaussianRat :=
  ⟨-26302089/125000000, 3935289/100000000⟩
def contact0207 : RatBall := localContactBall tau0207 center0207
def work0207 : RoundedTauEval :=
  evalTau precision tau0207 contact0207 logTwoBall

theorem center_sq0207 : (center0207.re : ℝ)^2 +
    (center0207.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0207]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0207 : work0207.theta.ok = true ∧
    work0207.jac.invOK = true ∧ acceptsUnitSq work0207.out = true := by
  norm_num [work0207, contact0207, tau0207, center0207, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0207 : CellCertificate where
  tauBall := tau0207
  contactCenter := center0207
  contactBall := contact0207
  work := work0207
  center_sq := center_sq0207
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0207.1
  jac_ok := checks0207.2.1
  accepted := checks0207.2.2

def cells : List CellCertificate := [cell0200, cell0201, cell0202, cell0203, cell0204, cell0205, cell0206, cell0207]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025
