import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0440 : RatBall :=
  ⟨⟨-5/32, -9/32⟩, 3/320⟩
def center0440 : GaussianRat :=
  ⟨-116565793/1000000000, -194890619/1000000000⟩
def contact0440 : RatBall := localContactBall tau0440 center0440
def work0440 : RoundedTauEval :=
  evalTau precision tau0440 contact0440 logTwoBall

theorem center_sq0440 : (center0440.re : ℝ)^2 +
    (center0440.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0440]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0440 : work0440.theta.ok = true ∧
    work0440.jac.invOK = true ∧ acceptsUnitSq work0440.out = true := by
  norm_num [work0440, contact0440, tau0440, center0440, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0440 : CellCertificate where
  tauBall := tau0440
  contactCenter := center0440
  contactBall := contact0440
  work := work0440
  center_sq := center_sq0440
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0440.1
  jac_ok := checks0440.2.1
  accepted := checks0440.2.2

def tau0441 : RatBall :=
  ⟨⟨-31/160, -43/160⟩, 3/320⟩
def center0441 : GaussianRat :=
  ⟨-71299541/500000000, -91537843/500000000⟩
def contact0441 : RatBall := localContactBall tau0441 center0441
def work0441 : RoundedTauEval :=
  evalTau precision tau0441 contact0441 logTwoBall

theorem center_sq0441 : (center0441.re : ℝ)^2 +
    (center0441.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0441]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0441 : work0441.theta.ok = true ∧
    work0441.jac.invOK = true ∧ acceptsUnitSq work0441.out = true := by
  norm_num [work0441, contact0441, tau0441, center0441, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0441 : CellCertificate where
  tauBall := tau0441
  contactCenter := center0441
  contactBall := contact0441
  work := work0441
  center_sq := center_sq0441
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0441.1
  jac_ok := checks0441.2.1
  accepted := checks0441.2.2

def tau0442 : RatBall :=
  ⟨⟨-29/160, -43/160⟩, 3/320⟩
def center0442 : GaussianRat :=
  ⟨-66845797/500000000, -18404523/100000000⟩
def contact0442 : RatBall := localContactBall tau0442 center0442
def work0442 : RoundedTauEval :=
  evalTau precision tau0442 contact0442 logTwoBall

theorem center_sq0442 : (center0442.re : ℝ)^2 +
    (center0442.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0442]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0442 : work0442.theta.ok = true ∧
    work0442.jac.invOK = true ∧ acceptsUnitSq work0442.out = true := by
  norm_num [work0442, contact0442, tau0442, center0442, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0442 : CellCertificate where
  tauBall := tau0442
  contactCenter := center0442
  contactBall := contact0442
  work := work0442
  center_sq := center_sq0442
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0442.1
  jac_ok := checks0442.2.1
  accepted := checks0442.2.2

def tau0443 : RatBall :=
  ⟨⟨-31/160, -41/160⟩, 3/320⟩
def center0443 : GaussianRat :=
  ⟨-8852011/62500000, -87111573/500000000⟩
def contact0443 : RatBall := localContactBall tau0443 center0443
def work0443 : RoundedTauEval :=
  evalTau precision tau0443 contact0443 logTwoBall

theorem center_sq0443 : (center0443.re : ℝ)^2 +
    (center0443.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0443]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0443 : work0443.theta.ok = true ∧
    work0443.jac.invOK = true ∧ acceptsUnitSq work0443.out = true := by
  norm_num [work0443, contact0443, tau0443, center0443, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0443 : CellCertificate where
  tauBall := tau0443
  contactCenter := center0443
  contactBall := contact0443
  work := work0443
  center_sq := center_sq0443
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0443.1
  jac_ok := checks0443.2.1
  accepted := checks0443.2.2

def tau0444 : RatBall :=
  ⟨⟨-29/160, -41/160⟩, 3/320⟩
def center0444 : GaussianRat :=
  ⟨-132776829/1000000000, -35027183/200000000⟩
def contact0444 : RatBall := localContactBall tau0444 center0444
def work0444 : RoundedTauEval :=
  evalTau precision tau0444 contact0444 logTwoBall

theorem center_sq0444 : (center0444.re : ℝ)^2 +
    (center0444.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0444]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0444 : work0444.theta.ok = true ∧
    work0444.jac.invOK = true ∧ acceptsUnitSq work0444.out = true := by
  norm_num [work0444, contact0444, tau0444, center0444, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0444 : CellCertificate where
  tauBall := tau0444
  contactCenter := center0444
  contactBall := contact0444
  work := work0444
  center_sq := center_sq0444
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0444.1
  jac_ok := checks0444.2.1
  accepted := checks0444.2.2

def tau0445 : RatBall :=
  ⟨⟨-27/160, -43/160⟩, 3/320⟩
def center0445 : GaussianRat :=
  ⟨-1948873/15625000, -92480083/500000000⟩
def contact0445 : RatBall := localContactBall tau0445 center0445
def work0445 : RoundedTauEval :=
  evalTau precision tau0445 contact0445 logTwoBall

theorem center_sq0445 : (center0445.re : ℝ)^2 +
    (center0445.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0445]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0445 : work0445.theta.ok = true ∧
    work0445.jac.invOK = true ∧ acceptsUnitSq work0445.out = true := by
  norm_num [work0445, contact0445, tau0445, center0445, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0445 : CellCertificate where
  tauBall := tau0445
  contactCenter := center0445
  contactBall := contact0445
  work := work0445
  center_sq := center_sq0445
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0445.1
  jac_ok := checks0445.2.1
  accepted := checks0445.2.2

def tau0446 : RatBall :=
  ⟨⟨-5/32, -43/160⟩, 3/320⟩
def center0446 : GaussianRat :=
  ⟨-57855523/500000000, -185818573/1000000000⟩
def contact0446 : RatBall := localContactBall tau0446 center0446
def work0446 : RoundedTauEval :=
  evalTau precision tau0446 contact0446 logTwoBall

theorem center_sq0446 : (center0446.re : ℝ)^2 +
    (center0446.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0446]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0446 : work0446.theta.ok = true ∧
    work0446.jac.invOK = true ∧ acceptsUnitSq work0446.out = true := by
  norm_num [work0446, contact0446, tau0446, center0446, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0446 : CellCertificate where
  tauBall := tau0446
  contactCenter := center0446
  contactBall := contact0446
  work := work0446
  center_sq := center_sq0446
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0446.1
  jac_ok := checks0446.2.1
  accepted := checks0446.2.2

def tau0447 : RatBall :=
  ⟨⟨-27/160, -41/160⟩, 3/320⟩
def center0447 : GaussianRat :=
  ⟨-123867137/1000000000, -21999637/125000000⟩
def contact0447 : RatBall := localContactBall tau0447 center0447
def work0447 : RoundedTauEval :=
  evalTau precision tau0447 contact0447 logTwoBall

theorem center_sq0447 : (center0447.re : ℝ)^2 +
    (center0447.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0447]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0447 : work0447.theta.ok = true ∧
    work0447.jac.invOK = true ∧ acceptsUnitSq work0447.out = true := by
  norm_num [work0447, contact0447, tau0447, center0447, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0447 : CellCertificate where
  tauBall := tau0447
  contactCenter := center0447
  contactBall := contact0447
  work := work0447
  center_sq := center_sq0447
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0447.1
  jac_ok := checks0447.2.1
  accepted := checks0447.2.2

def cells : List CellCertificate := [cell0440, cell0441, cell0442, cell0443, cell0444, cell0445, cell0446, cell0447]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055
