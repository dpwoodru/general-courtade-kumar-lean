import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0304 : RatBall :=
  ⟨⟨31/80, 1/80⟩, 3/160⟩
def center0304 : GaussianRat :=
  ⟨255809887/1000000000, 749167/100000000⟩
def contact0304 : RatBall := localContactBall tau0304 center0304
def work0304 : RoundedTauEval :=
  evalTau precision tau0304 contact0304 logTwoBall

theorem center_sq0304 : (center0304.re : ℝ)^2 +
    (center0304.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0304]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0304 : work0304.theta.ok = true ∧
    work0304.jac.invOK = true ∧ acceptsUnitSq work0304.out = true := by
  norm_num [work0304, contact0304, tau0304, center0304, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0304 : CellCertificate where
  tauBall := tau0304
  contactCenter := center0304
  contactBall := contact0304
  work := work0304
  center_sq := center_sq0304
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0304.1
  jac_ok := checks0304.2.1
  accepted := checks0304.2.2

def tau0305 : RatBall :=
  ⟨⟨29/80, 3/80⟩, 3/160⟩
def center0305 : GaussianRat :=
  ⟨120475049/500000000, 4573419/200000000⟩
def contact0305 : RatBall := localContactBall tau0305 center0305
def work0305 : RoundedTauEval :=
  evalTau precision tau0305 contact0305 logTwoBall

theorem center_sq0305 : (center0305.re : ℝ)^2 +
    (center0305.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0305]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0305 : work0305.theta.ok = true ∧
    work0305.jac.invOK = true ∧ acceptsUnitSq work0305.out = true := by
  norm_num [work0305, contact0305, tau0305, center0305, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0305 : CellCertificate where
  tauBall := tau0305
  contactCenter := center0305
  contactBall := contact0305
  work := work0305
  center_sq := center_sq0305
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0305.1
  jac_ok := checks0305.2.1
  accepted := checks0305.2.2

def tau0306 : RatBall :=
  ⟨⟨5/16, 1/16⟩, 3/160⟩
def center0306 : GaussianRat :=
  ⟨26302089/125000000, 3935289/100000000⟩
def contact0306 : RatBall := localContactBall tau0306 center0306
def work0306 : RoundedTauEval :=
  evalTau precision tau0306 contact0306 logTwoBall

theorem center_sq0306 : (center0306.re : ℝ)^2 +
    (center0306.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0306]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0306 : work0306.theta.ok = true ∧
    work0306.jac.invOK = true ∧ acceptsUnitSq work0306.out = true := by
  norm_num [work0306, contact0306, tau0306, center0306, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0306 : CellCertificate where
  tauBall := tau0306
  contactCenter := center0306
  contactBall := contact0306
  work := work0306
  center_sq := center_sq0306
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0306.1
  jac_ok := checks0306.2.1
  accepted := checks0306.2.2

def tau0307 : RatBall :=
  ⟨⟨27/80, 1/16⟩, 3/160⟩
def center0307 : GaussianRat :=
  ⟨22606221/100000000, 4844151/125000000⟩
def contact0307 : RatBall := localContactBall tau0307 center0307
def work0307 : RoundedTauEval :=
  evalTau precision tau0307 contact0307 logTwoBall

theorem center_sq0307 : (center0307.re : ℝ)^2 +
    (center0307.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0307]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0307 : work0307.theta.ok = true ∧
    work0307.jac.invOK = true ∧ acceptsUnitSq work0307.out = true := by
  norm_num [work0307, contact0307, tau0307, center0307, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0307 : CellCertificate where
  tauBall := tau0307
  contactCenter := center0307
  contactBall := contact0307
  work := work0307
  center_sq := center_sq0307
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0307.1
  jac_ok := checks0307.2.1
  accepted := checks0307.2.2

def tau0308 : RatBall :=
  ⟨⟨5/16, 7/80⟩, 3/160⟩
def center0308 : GaussianRat :=
  ⟨211121197/1000000000, 55135609/1000000000⟩
def contact0308 : RatBall := localContactBall tau0308 center0308
def work0308 : RoundedTauEval :=
  evalTau precision tau0308 contact0308 logTwoBall

theorem center_sq0308 : (center0308.re : ℝ)^2 +
    (center0308.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0308]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0308 : work0308.theta.ok = true ∧
    work0308.jac.invOK = true ∧ acceptsUnitSq work0308.out = true := by
  norm_num [work0308, contact0308, tau0308, center0308, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0308 : CellCertificate where
  tauBall := tau0308
  contactCenter := center0308
  contactBall := contact0308
  work := work0308
  center_sq := center_sq0308
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0308.1
  jac_ok := checks0308.2.1
  accepted := checks0308.2.2

def tau0309 : RatBall :=
  ⟨⟨27/80, 7/80⟩, 3/160⟩
def center0309 : GaussianRat :=
  ⟨14175019/62500000, 54291363/1000000000⟩
def contact0309 : RatBall := localContactBall tau0309 center0309
def work0309 : RoundedTauEval :=
  evalTau precision tau0309 contact0309 logTwoBall

theorem center_sq0309 : (center0309.re : ℝ)^2 +
    (center0309.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0309]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0309 : work0309.theta.ok = true ∧
    work0309.jac.invOK = true ∧ acceptsUnitSq work0309.out = true := by
  norm_num [work0309, contact0309, tau0309, center0309, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0309 : CellCertificate where
  tauBall := tau0309
  contactCenter := center0309
  contactBall := contact0309
  work := work0309
  center_sq := center_sq0309
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0309.1
  jac_ok := checks0309.2.1
  accepted := checks0309.2.2

def tau0310 : RatBall :=
  ⟨⟨29/80, 1/16⟩, 3/160⟩
def center0310 : GaussianRat :=
  ⟨241459683/1000000000, 9531797/250000000⟩
def contact0310 : RatBall := localContactBall tau0310 center0310
def work0310 : RoundedTauEval :=
  evalTau precision tau0310 contact0310 logTwoBall

theorem center_sq0310 : (center0310.re : ℝ)^2 +
    (center0310.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0310]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0310 : work0310.theta.ok = true ∧
    work0310.jac.invOK = true ∧ acceptsUnitSq work0310.out = true := by
  norm_num [work0310, contact0310, tau0310, center0310, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0310 : CellCertificate where
  tauBall := tau0310
  contactCenter := center0310
  contactBall := contact0310
  work := work0310
  center_sq := center_sq0310
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0310.1
  jac_ok := checks0310.2.1
  accepted := checks0310.2.2

def tau0311 : RatBall :=
  ⟨⟨17/80, 9/80⟩, 3/160⟩
def center0311 : GaussianRat :=
  ⟨29368329/200000000, 18684497/250000000⟩
def contact0311 : RatBall := localContactBall tau0311 center0311
def work0311 : RoundedTauEval :=
  evalTau precision tau0311 contact0311 logTwoBall

theorem center_sq0311 : (center0311.re : ℝ)^2 +
    (center0311.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0311]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0311 : work0311.theta.ok = true ∧
    work0311.jac.invOK = true ∧ acceptsUnitSq work0311.out = true := by
  norm_num [work0311, contact0311, tau0311, center0311, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0311 : CellCertificate where
  tauBall := tau0311
  contactCenter := center0311
  contactBall := contact0311
  work := work0311
  center_sq := center_sq0311
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0311.1
  jac_ok := checks0311.2.1
  accepted := checks0311.2.2

def cells : List CellCertificate := [cell0304, cell0305, cell0306, cell0307, cell0308, cell0309, cell0310, cell0311]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038
