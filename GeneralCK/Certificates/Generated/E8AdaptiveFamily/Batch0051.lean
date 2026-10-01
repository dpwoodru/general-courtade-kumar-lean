import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0408 : RatBall :=
  ⟨⟨-9/160, -53/160⟩, 3/320⟩
def center0408 : GaussianRat :=
  ⟨-43918333/1000000000, -238021713/1000000000⟩
def contact0408 : RatBall := localContactBall tau0408 center0408
def work0408 : RoundedTauEval :=
  evalTau precision tau0408 contact0408 logTwoBall

theorem center_sq0408 : (center0408.re : ℝ)^2 +
    (center0408.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0408]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0408 : work0408.theta.ok = true ∧
    work0408.jac.invOK = true ∧ acceptsUnitSq work0408.out = true := by
  norm_num [work0408, contact0408, tau0408, center0408, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0408 : CellCertificate where
  tauBall := tau0408
  contactCenter := center0408
  contactBall := contact0408
  work := work0408
  center_sq := center_sq0408
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0408.1
  jac_ok := checks0408.2.1
  accepted := checks0408.2.2

def tau0409 : RatBall :=
  ⟨⟨-3/32, -51/160⟩, 3/320⟩
def center0409 : GaussianRat :=
  ⟨-18071427/250000000, -113380411/500000000⟩
def contact0409 : RatBall := localContactBall tau0409 center0409
def work0409 : RoundedTauEval :=
  evalTau precision tau0409 contact0409 logTwoBall

theorem center_sq0409 : (center0409.re : ℝ)^2 +
    (center0409.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0409]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0409 : work0409.theta.ok = true ∧
    work0409.jac.invOK = true ∧ acceptsUnitSq work0409.out = true := by
  norm_num [work0409, contact0409, tau0409, center0409, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0409 : CellCertificate where
  tauBall := tau0409
  contactCenter := center0409
  contactBall := contact0409
  work := work0409
  center_sq := center_sq0409
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0409.1
  jac_ok := checks0409.2.1
  accepted := checks0409.2.2

def tau0410 : RatBall :=
  ⟨⟨-13/160, -51/160⟩, 3/320⟩
def center0410 : GaussianRat :=
  ⟨-2508961/40000000, -56843321/250000000⟩
def contact0410 : RatBall := localContactBall tau0410 center0410
def work0410 : RoundedTauEval :=
  evalTau precision tau0410 contact0410 logTwoBall

theorem center_sq0410 : (center0410.re : ℝ)^2 +
    (center0410.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0410]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0410 : work0410.theta.ok = true ∧
    work0410.jac.invOK = true ∧ acceptsUnitSq work0410.out = true := by
  norm_num [work0410, contact0410, tau0410, center0410, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0410 : CellCertificate where
  tauBall := tau0410
  contactCenter := center0410
  contactBall := contact0410
  work := work0410
  center_sq := center_sq0410
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0410.1
  jac_ok := checks0410.2.1
  accepted := checks0410.2.2

def tau0411 : RatBall :=
  ⟨⟨-3/32, -49/160⟩, 3/320⟩
def center0411 : GaussianRat :=
  ⟨-14329959/200000000, -108628837/500000000⟩
def contact0411 : RatBall := localContactBall tau0411 center0411
def work0411 : RoundedTauEval :=
  evalTau precision tau0411 contact0411 logTwoBall

theorem center_sq0411 : (center0411.re : ℝ)^2 +
    (center0411.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0411]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0411 : work0411.theta.ok = true ∧
    work0411.jac.invOK = true ∧ acceptsUnitSq work0411.out = true := by
  norm_num [work0411, contact0411, tau0411, center0411, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0411 : CellCertificate where
  tauBall := tau0411
  contactCenter := center0411
  contactBall := contact0411
  work := work0411
  center_sq := center_sq0411
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0411.1
  jac_ok := checks0411.2.1
  accepted := checks0411.2.2

def tau0412 : RatBall :=
  ⟨⟨-13/160, -49/160⟩, 3/320⟩
def center0412 : GaussianRat :=
  ⟨-3885599/62500000, -6807377/31250000⟩
def contact0412 : RatBall := localContactBall tau0412 center0412
def work0412 : RoundedTauEval :=
  evalTau precision tau0412 contact0412 logTwoBall

theorem center_sq0412 : (center0412.re : ℝ)^2 +
    (center0412.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0412]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0412 : work0412.theta.ok = true ∧
    work0412.jac.invOK = true ∧ acceptsUnitSq work0412.out = true := by
  norm_num [work0412, contact0412, tau0412, center0412, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0412 : CellCertificate where
  tauBall := tau0412
  contactCenter := center0412
  contactBall := contact0412
  work := work0412
  center_sq := center_sq0412
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0412.1
  jac_ok := checks0412.2.1
  accepted := checks0412.2.2

def tau0413 : RatBall :=
  ⟨⟨-11/160, -51/160⟩, 3/320⟩
def center0413 : GaussianRat :=
  ⟨-53129867/1000000000, -56975307/250000000⟩
def contact0413 : RatBall := localContactBall tau0413 center0413
def work0413 : RoundedTauEval :=
  evalTau precision tau0413 contact0413 logTwoBall

theorem center_sq0413 : (center0413.re : ℝ)^2 +
    (center0413.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0413]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0413 : work0413.theta.ok = true ∧
    work0413.jac.invOK = true ∧ acceptsUnitSq work0413.out = true := by
  norm_num [work0413, contact0413, tau0413, center0413, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0413 : CellCertificate where
  tauBall := tau0413
  contactCenter := center0413
  contactBall := contact0413
  work := work0413
  center_sq := center_sq0413
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0413.1
  jac_ok := checks0413.2.1
  accepted := checks0413.2.2

def tau0414 : RatBall :=
  ⟨⟨-9/160, -51/160⟩, 3/320⟩
def center0414 : GaussianRat :=
  ⟨-21754011/500000000, -445983/1953125⟩
def contact0414 : RatBall := localContactBall tau0414 center0414
def work0414 : RoundedTauEval :=
  evalTau precision tau0414 contact0414 logTwoBall

theorem center_sq0414 : (center0414.re : ℝ)^2 +
    (center0414.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0414]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0414 : work0414.theta.ok = true ∧
    work0414.jac.invOK = true ∧ acceptsUnitSq work0414.out = true := by
  norm_num [work0414, contact0414, tau0414, center0414, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0414 : CellCertificate where
  tauBall := tau0414
  contactCenter := center0414
  contactBall := contact0414
  work := work0414
  center_sq := center_sq0414
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0414.1
  jac_ok := checks0414.2.1
  accepted := checks0414.2.2

def tau0415 : RatBall :=
  ⟨⟨-11/160, -49/160⟩, 3/320⟩
def center0415 : GaussianRat :=
  ⟨-52658297/1000000000, -109167283/500000000⟩
def contact0415 : RatBall := localContactBall tau0415 center0415
def work0415 : RoundedTauEval :=
  evalTau precision tau0415 contact0415 logTwoBall

theorem center_sq0415 : (center0415.re : ℝ)^2 +
    (center0415.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0415]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0415 : work0415.theta.ok = true ∧
    work0415.jac.invOK = true ∧ acceptsUnitSq work0415.out = true := by
  norm_num [work0415, contact0415, tau0415, center0415, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0415 : CellCertificate where
  tauBall := tau0415
  contactCenter := center0415
  contactBall := contact0415
  work := work0415
  center_sq := center_sq0415
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0415.1
  jac_ok := checks0415.2.1
  accepted := checks0415.2.2

def cells : List CellCertificate := [cell0408, cell0409, cell0410, cell0411, cell0412, cell0413, cell0414, cell0415]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051
