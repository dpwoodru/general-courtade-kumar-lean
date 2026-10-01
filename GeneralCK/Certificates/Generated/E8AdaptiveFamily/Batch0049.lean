import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0049

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0392 : RatBall :=
  ⟨⟨-33/160, -33/160⟩, 3/320⟩
def center0392 : GaussianRat :=
  ⟨-73472183/500000000, -69270487/500000000⟩
def contact0392 : RatBall := localContactBall tau0392 center0392
def work0392 : RoundedTauEval :=
  evalTau precision tau0392 contact0392 logTwoBall

theorem center_sq0392 : (center0392.re : ℝ)^2 +
    (center0392.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0392]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0392 : work0392.theta.ok = true ∧
    work0392.jac.invOK = true ∧ acceptsUnitSq work0392.out = true := by
  norm_num [work0392, contact0392, tau0392, center0392, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0392 : CellCertificate where
  tauBall := tau0392
  contactCenter := center0392
  contactBall := contact0392
  work := work0392
  center_sq := center_sq0392
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0392.1
  jac_ok := checks0392.2.1
  accepted := checks0392.2.2

def tau0393 : RatBall :=
  ⟨⟨-27/160, -49/160⟩, 3/320⟩
def center0393 : GaussianRat :=
  ⟨-3988651/31250000, -53050431/250000000⟩
def contact0393 : RatBall := localContactBall tau0393 center0393
def work0393 : RoundedTauEval :=
  evalTau precision tau0393 contact0393 logTwoBall

theorem center_sq0393 : (center0393.re : ℝ)^2 +
    (center0393.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0393]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0393 : work0393.theta.ok = true ∧
    work0393.jac.invOK = true ∧ acceptsUnitSq work0393.out = true := by
  norm_num [work0393, contact0393, tau0393, center0393, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0393 : CellCertificate where
  tauBall := tau0393
  contactCenter := center0393
  contactBall := contact0393
  work := work0393
  center_sq := center_sq0393
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0393.1
  jac_ok := checks0393.2.1
  accepted := checks0393.2.2

def tau0394 : RatBall :=
  ⟨⟨-5/32, -49/160⟩, 3/320⟩
def center0394 : GaussianRat :=
  ⟨-23686489/200000000, -53305887/250000000⟩
def contact0394 : RatBall := localContactBall tau0394 center0394
def work0394 : RoundedTauEval :=
  evalTau precision tau0394 contact0394 logTwoBall

theorem center_sq0394 : (center0394.re : ℝ)^2 +
    (center0394.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0394]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0394 : work0394.theta.ok = true ∧
    work0394.jac.invOK = true ∧ acceptsUnitSq work0394.out = true := by
  norm_num [work0394, contact0394, tau0394, center0394, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0394 : CellCertificate where
  tauBall := tau0394
  contactCenter := center0394
  contactBall := contact0394
  work := work0394
  center_sq := center_sq0394
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0394.1
  jac_ok := checks0394.2.1
  accepted := checks0394.2.2

def tau0395 : RatBall :=
  ⟨⟨-17/160, -53/160⟩, 3/320⟩
def center0395 : GaussianRat :=
  ⟨-82567747/1000000000, -117805603/500000000⟩
def contact0395 : RatBall := localContactBall tau0395 center0395
def work0395 : RoundedTauEval :=
  evalTau precision tau0395 contact0395 logTwoBall

theorem center_sq0395 : (center0395.re : ℝ)^2 +
    (center0395.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0395]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0395 : work0395.theta.ok = true ∧
    work0395.jac.invOK = true ∧ acceptsUnitSq work0395.out = true := by
  norm_num [work0395, contact0395, tau0395, center0395, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0395 : CellCertificate where
  tauBall := tau0395
  contactCenter := center0395
  contactBall := contact0395
  work := work0395
  center_sq := center_sq0395
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0395.1
  jac_ok := checks0395.2.1
  accepted := checks0395.2.2

def tau0396 : RatBall :=
  ⟨⟨-21/160, -51/160⟩, 3/320⟩
def center0396 : GaussianRat :=
  ⟨-100729897/1000000000, -44886561/200000000⟩
def contact0396 : RatBall := localContactBall tau0396 center0396
def work0396 : RoundedTauEval :=
  evalTau precision tau0396 contact0396 logTwoBall

theorem center_sq0396 : (center0396.re : ℝ)^2 +
    (center0396.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0396]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0396 : work0396.theta.ok = true ∧
    work0396.jac.invOK = true ∧ acceptsUnitSq work0396.out = true := by
  norm_num [work0396, contact0396, tau0396, center0396, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0396 : CellCertificate where
  tauBall := tau0396
  contactCenter := center0396
  contactBall := contact0396
  work := work0396
  center_sq := center_sq0396
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0396.1
  jac_ok := checks0396.2.1
  accepted := checks0396.2.2

def tau0397 : RatBall :=
  ⟨⟨-23/160, -49/160⟩, 3/320⟩
def center0397 : GaussianRat :=
  ⟨-109172181/1000000000, -42835301/200000000⟩
def contact0397 : RatBall := localContactBall tau0397 center0397
def work0397 : RoundedTauEval :=
  evalTau precision tau0397 contact0397 logTwoBall

theorem center_sq0397 : (center0397.re : ℝ)^2 +
    (center0397.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0397]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0397 : work0397.theta.ok = true ∧
    work0397.jac.invOK = true ∧ acceptsUnitSq work0397.out = true := by
  norm_num [work0397, contact0397, tau0397, center0397, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0397 : CellCertificate where
  tauBall := tau0397
  contactCenter := center0397
  contactBall := contact0397
  work := work0397
  center_sq := center_sq0397
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0397.1
  jac_ok := checks0397.2.1
  accepted := checks0397.2.2

def tau0398 : RatBall :=
  ⟨⟨-21/160, -49/160⟩, 3/320⟩
def center0398 : GaussianRat :=
  ⟨-9985979/100000000, -43011679/200000000⟩
def contact0398 : RatBall := localContactBall tau0398 center0398
def work0398 : RoundedTauEval :=
  evalTau precision tau0398 contact0398 logTwoBall

theorem center_sq0398 : (center0398.re : ℝ)^2 +
    (center0398.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0398]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0398 : work0398.theta.ok = true ∧
    work0398.jac.invOK = true ∧ acceptsUnitSq work0398.out = true := by
  norm_num [work0398, contact0398, tau0398, center0398, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0398 : CellCertificate where
  tauBall := tau0398
  contactCenter := center0398
  contactBall := contact0398
  work := work0398
  center_sq := center_sq0398
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0398.1
  jac_ok := checks0398.2.1
  accepted := checks0398.2.2

def tau0399 : RatBall :=
  ⟨⟨-19/160, -51/160⟩, 3/320⟩
def center0399 : GaussianRat :=
  ⟨-18258621/200000000, -56322187/250000000⟩
def contact0399 : RatBall := localContactBall tau0399 center0399
def work0399 : RoundedTauEval :=
  evalTau precision tau0399 contact0399 logTwoBall

theorem center_sq0399 : (center0399.re : ℝ)^2 +
    (center0399.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0399]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0399 : work0399.theta.ok = true ∧
    work0399.jac.invOK = true ∧ acceptsUnitSq work0399.out = true := by
  norm_num [work0399, contact0399, tau0399, center0399, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0399 : CellCertificate where
  tauBall := tau0399
  contactCenter := center0399
  contactBall := contact0399
  work := work0399
  center_sq := center_sq0399
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0399.1
  jac_ok := checks0399.2.1
  accepted := checks0399.2.2

def cells : List CellCertificate := [cell0392, cell0393, cell0394, cell0395, cell0396, cell0397, cell0398, cell0399]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0049
